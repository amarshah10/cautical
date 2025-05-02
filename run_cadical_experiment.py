#!/usr/bin/env python3

import argparse
import concurrent.futures
import datetime
import os
import subprocess
import sys
import time
from pathlib import Path
import shutil
def run_cadical(file_path, proof_path, timeout, produce_proofs, check_proofs, solver, prelearn_timeout):
    start_time = time.time()
    try:
        if solver == "prelearn":
            # Create prelearn directory
            prelearn_dir = Path("prelearn") / file_path.stem
            prelearn_dir.mkdir(parents=True, exist_ok=True)
            
            # Get absolute paths
            abs_file_path = file_path.absolute()
            abs_sadical_path = Path("../PReLearn/PReLearn/sadical").absolute()
            
            # Phase 1: Run PReLearn
            phase1_start = time.time()
            phase1_cmd = [str(abs_sadical_path), "--pre_iterations=50", str(abs_file_path)]
            try:
                phase1_result = subprocess.run(
                    phase1_cmd,
                    capture_output=True,
                    text=True,
                    timeout=prelearn_timeout,
                    cwd=str(prelearn_dir)
                )
                phase1_time = time.time() - phase1_start
                
                if phase1_result.returncode != 0:
                    print("PReLearn failed")
                    shutil.rmtree(prelearn_dir) 
                    return {
                        "file_name": file_path.name,
                        "status": "ERR: PReLearn failed",
                        "runtime": phase1_time,
                        "phase1_time": phase1_time,
                        "phase2_time": 0,
                        "proof_status": None,
                        "proof_time": None,
                        "assignment": None
                    }
            except subprocess.TimeoutExpired:
                phase1_time = prelearn_timeout
                # print("PReLearn timed out, continuing with original file")
                # Use original file instead of combined file
                combined_path = file_path
            
            # Read original file header
            with open(file_path, 'r') as f:
                header = f.readline().strip()
                while header.startswith('c'):
                    header = f.readline().strip()
                _, _, num_vars, num_clauses = header.split()
                num_clauses = int(num_clauses)
            
            # Only create combined file if PReLearn didn't timeout
            if phase1_time < prelearn_timeout:
                # Read pr_clauses.cnf and count lines
                pr_clauses_path = prelearn_dir / "pr_clauses.cnf"
                with open(pr_clauses_path, 'r') as f:
                    pr_lines = [line for line in f if not line.startswith('c') and line.strip()]
                    num_pr_clauses = len(pr_lines)
                
                # Create combined file
                combined_path = prelearn_dir / f"{file_path.stem}_with_pr.cnf"
                # print(f"Creating combined file at: {combined_path}")
                # print(f"Original file: {file_path}")
                # print(f"PR clauses file: {pr_clauses_path}")
                
                # Verify files exist
                if not file_path.exists():
                    print(f"ERROR: Original file does not exist: {file_path}")
                    shutil.rmtree(prelearn_dir) 
                    return {
                        "file_name": file_path.name,
                        "status": "ERR: Original file missing",
                        "runtime": phase1_time,
                        "phase1_time": phase1_time,
                        "phase2_time": 0,
                        "proof_status": None,
                        "proof_time": None,
                        "assignment": None
                    }
                
                if not pr_clauses_path.exists():
                    print(f"ERROR: PR clauses file does not exist: {pr_clauses_path}")
                    shutil.rmtree(prelearn_dir) 
                    return {
                        "file_name": file_path.name,
                        "status": "ERR: PR clauses file missing",
                        "runtime": phase1_time,
                        "phase1_time": phase1_time,
                        "phase2_time": 0,
                        "proof_status": None,
                        "proof_time": None,
                        "assignment": None
                    }
                
                with open(combined_path, 'w') as out_f:
                    # Write modified header
                    out_f.write(f"p cnf {num_vars} {num_clauses + num_pr_clauses}\n")
                    # Write original clauses
                    with open(file_path, 'r') as in_f:
                        for line in in_f:
                            if not line.startswith('p cnf'):
                                out_f.write(line)
                    # Write PR clauses
                    out_f.writelines(pr_lines)
                
                # Verify combined file was created
                if not combined_path.exists():
                    print(f"ERROR: Combined file was not created: {combined_path}")
                    shutil.rmtree(prelearn_dir) 
                    return {
                        "file_name": file_path.name,
                        "status": "ERR: Combined file creation failed",
                        "runtime": phase1_time,
                        "phase1_time": phase1_time,
                        "phase2_time": 0,
                        "proof_status": None,
                        "proof_time": None,
                        "assignment": None
                    }
                
                # print(f"Successfully created combined file with {num_clauses + num_pr_clauses} clauses")
            
            # Phase 2: Run CaDiCaL on combined file
            phase2_start = time.time()
            # print("Starting on phase 2")
            abs_cadical_path = "/home/amarshah/cadical/build/cadical"
            abs_combined_path = combined_path.absolute()
            phase2_cmd = [str(abs_cadical_path), str(abs_combined_path)]
            if produce_proofs:
                absolute_proof_path = proof_path.absolute()
                phase2_cmd.append(str(absolute_proof_path))
            
            phase2_result = subprocess.run(
                phase2_cmd,
                capture_output=True,
                text=True,
                timeout=timeout,
                cwd=str(prelearn_dir)
            )
            phase2_time = time.time() - phase2_start

            # print(f"finished phase 2 running {phase2_result.returncode}")
            
            # Determine result and capture assignment if SAT
            assignment = []
            if phase2_result.returncode == 10:
                status = "SAT"
                # Get the last 100 lines and find the assignment
                lines = phase2_result.stdout.split('\n')[-1000:]
                for line in lines:
                    if line.startswith('v '):
                        assignment += line.split(" ")[1:]
            elif phase2_result.returncode == 20:
                status = "UNSAT"
            else:
                status = f"ERR: {phase2_result.returncode}"
                print(phase2_cmd)
                print(phase2_result.stdout)
                print(phase2_result.stderr)
            
            # Clean up prelearn directory
            # print("Cleaning up prelearn directory")
            shutil.rmtree(prelearn_dir)
            
            return {
                "file_name": file_path.name,
                "status": status,
                "runtime": phase1_time + phase2_time,
                "phase1_time": phase1_time,
                "phase2_time": phase2_time,
                "proof_status": None,  # PReLearn proofs are not verified
                "proof_time": None,
                "assignment": assignment
            }
            
        else:  # cautical or cadical
            # Run CaDiCaL
            if solver == "cautical":
                cmd = ["build/cadical", "--globalpreprocess", str(file_path)]
                env = os.environ.copy()
                env["CADICAL_FILENAME"] = "l.t"
            else:  # cadical
                cmd = ["../cadical/build/cadical", str(file_path)]
                env = None
            
            if produce_proofs:
                cmd.append(str(proof_path))
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout,
                env=env
            )
            
            # Determine result and capture assignment if SAT
            assignment = []
            if result.returncode == 10:
                status = "SAT"
                # Get the last 100 lines and find the assignment
                lines = result.stdout.split('\n')[-1000:]
                for line in lines:
                    if line.startswith('v '):
                        assignment += line.split(" ")[1:]
            elif result.returncode == 20:
                status = "UNSAT"
            else:
                status = f"ERR: {result.returncode}"
                print(cmd.join(" "))
                
            runtime = time.time() - start_time
            
            # Verify proof if requested
            proof_status = None
            proof_time = None
            if check_proofs and result.returncode == 20:  # Only verify UNSAT proofs
                try:
                    verify_start = time.time()
                    verify_cmd = ["../dpr-trim/dpr-trim", str(file_path), str(proof_path)]
                    verify_result = subprocess.run(
                        verify_cmd,
                        capture_output=True,
                        text=True,
                        timeout=timeout
                    )
                    proof_time = time.time() - verify_start
                    proof_status = "VERIFIED" if "s VERIFIED" in verify_result.stdout else "NOT VERIFIED"
                except subprocess.TimeoutExpired:
                    proof_status = "TIMEOUT"
                    proof_time = timeout
            
            return {
                "file_name": file_path.name,
                "status": status,
                "runtime": runtime,
                "phase1_time": None,
                "phase2_time": None,
                "proof_status": proof_status,
                "proof_time": proof_time,
                "assignment": assignment
            }
            
    except subprocess.TimeoutExpired:
        return {
            "file_name": file_path.name,
            "status": "TIMEOUT",
            "runtime": timeout,
            "phase1_time": None,
            "phase2_time": None,
            "proof_status": None,
            "proof_time": None,
            "assignment": None
        }
    finally:
        # Clean up proof file if it exists and we produced proofs
        if produce_proofs and proof_path.exists():
            proof_path.unlink()

def main():
    parser = argparse.ArgumentParser(description="Run CaDiCaL experiments in parallel")
    parser.add_argument("--folder", default="../satcomp_benchmarks_fixed",
                      help="Folder containing input files")
    parser.add_argument("--timeout", type=int, default=100,
                      help="Timeout in seconds")
    parser.add_argument("--prelearn_timeout", type=int, default=100,
                      help="Timeout for PReLearn phase in seconds")
    parser.add_argument("--produce_proofs", action="store_true",
                      help="Enable proof production")
    parser.add_argument("--check_proofs", action="store_true",
                      help="Enable proof checking (requires --produce_proofs)")
    parser.add_argument("--output_file", default=None,
                      help="Output file path")
    parser.add_argument("--cores", type=int, default=7,
                      help="Number of cores to use")
    parser.add_argument("--solver", choices=["cautical", "cadical", "prelearn"], default="cautical",
                      help="Solver to use")
    
    args = parser.parse_args()
    
    # Validate arguments
    if args.check_proofs and not args.produce_proofs:
        parser.error("--check_proofs requires --produce_proofs")
    if args.check_proofs and args.solver == "prelearn":
        print("Warning: Proof verification is not supported for PReLearn solver")
    
    # Set up output file
    if args.output_file is None:
        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        args.output_file = f"results/python_experiment_{Path(args.folder).name}_{args.timeout}_prod{args.produce_proofs}_check{args.check_proofs}_{args.solver}_{timestamp}.txt"
    
    # Get all input files
    input_folder = Path(args.folder)
    input_files = list(input_folder.glob("*.cnf"))
    
    # Create proof directory
    proof_dir = Path("proofs")
    proof_dir.mkdir(exist_ok=True)
    
    # Statistics tracking
    sat_times = []
    unsat_times = []
    sat_count = 0
    unsat_count = 0
    timeout_count = 0
    error_count = 0
    
    # Open output file
    with open(args.output_file, "w") as f:
        start_time = datetime.datetime.now()
        f.write(f"Experiment started at: {start_time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Input folder: {args.folder}\n")
        f.write(f"Solver: {args.solver}\n")
        f.write(f"Timeout: {args.timeout}s\n")
        if args.solver == "prelearn":
            f.write(f"PReLearn timeout: {args.prelearn_timeout}s\n")
        f.write(f"Produce proofs: {args.produce_proofs}\n")
        f.write(f"Check proofs: {args.check_proofs}\n")
        f.write(f"Number of cores: {args.cores}\n")
        f.write(f"Number of instances: {len(input_files)}\n")
        f.write("-" * 80 + "\n")
        
        # Run experiments in parallel
        with concurrent.futures.ProcessPoolExecutor(max_workers=args.cores) as executor:
            futures = []
            for file_path in input_files:
                proof_path = proof_dir / f"{file_path.stem}.pr"
                futures.append(
                    executor.submit(run_cadical, file_path, proof_path, args.timeout, args.produce_proofs, args.check_proofs, args.solver, args.prelearn_timeout)
                )
            
            for future in concurrent.futures.as_completed(futures):
                result = future.result()
                
                # Print solving result immediately
                solving_output = f"{result['file_name']}: {result['status']} ({result['runtime']:.2f}s)"
                if args.solver == "prelearn" and result['phase1_time'] is not None and result['phase2_time'] is not None:
                    solving_output += f" [PReLearn: {result['phase1_time']:.2f}s, CaDiCaL: {result['phase2_time']:.2f}s]"
                print(solving_output)
                f.write(solving_output + "\n")
                
                # Print assignment if SAT
                if result['status'] == "SAT" and result['assignment']:
                    print(result['assignment'])
                    f.write(result['assignment'].join(" ") + "\n")
                
                # Print verification result separately if available
                if args.check_proofs and result['proof_status']:
                    verify_output = f"{result['file_name']}: Proof {result['proof_status']} ({result['proof_time']:.2f}s)"
                    print(verify_output)
                    f.write(verify_output + "\n")
                
                f.flush()
                
                # Update statistics
                if result['status'] == "SAT":
                    sat_count += 1
                    sat_times.append(result['runtime'])
                elif result['status'] == "UNSAT":
                    unsat_count += 1
                    unsat_times.append(result['runtime'])
                elif result['status'] == "TIMEOUT":
                    timeout_count += 1
                else:
                    error_count += 1
        
        # Calculate statistics
        end_time = datetime.datetime.now()
        duration = end_time - start_time
        
        # Calculate medians
        sat_median = sorted(sat_times)[len(sat_times)//2] if sat_times else "N/A"
        unsat_median = sorted(unsat_times)[len(unsat_times)//2] if unsat_times else "N/A"
        
        # Write summary
        f.write("\n" + "=" * 80 + "\n")
        f.write("Experiment Summary:\n")
        f.write(f"Finished at: {end_time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Total duration: {duration}\n")
        f.write(f"SAT instances: {sat_count}\n")
        f.write(f"UNSAT instances: {unsat_count}\n")
        f.write(f"TIMEOUT instances: {timeout_count}\n")
        f.write(f"ERROR instances: {error_count}\n")
        f.write(f"Median SAT time: {sat_median}s\n")
        f.write(f"Median UNSAT time: {unsat_median}s\n")

if __name__ == "__main__":
    main() 