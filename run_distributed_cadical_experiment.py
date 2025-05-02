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
from pssh.clients import ParallelSSHClient
from pssh.utils import enable_host_logger
import logging
import json
from typing import List, Dict, Any

# Configure logging
enable_host_logger()
logging.basicConfig(level=logging.INFO)

# List of remote hosts with their core counts
REMOTE_HOSTS = {
    'serenity-9900k-627e.andrew.cmu.edu': 7,  # s1901
    'serenity-9900k-61dd.andrew.cmu.edu': 7,  # s1902
    'serenity-9900k-81d5.andrew.cmu.edu': 7,  # s1905
    'serenity-9900k-81a1.andrew.cmu.edu': 7,  # s1906
    'serenity-9900k-63eb.andrew.cmu.edu': 7,  # s1907
    'serenity-9900k-6302.andrew.cmu.edu': 7,  # s1908
    'genesis-10980xe-f73c.andrew.cmu.edu': 30  # g2001
}

# Directories to copy
DIRECTORIES_TO_COPY = [
    '../cadical',
    '../cautical',
    '../dpr-trim',
    '../satcomp_benchmarks22',
    # '../satcomp_benchmarks23',
    # '../satcomp_benchmarks24',
    '../PReLearn'
]

def copy_directories_to_remote(host: str, use_compression: bool = False, exclude_patterns: List[str] = None) -> bool:
    """Copy required directories to remote host."""
    try:
        # Create remote home directory if it doesn't exist
        subprocess.run(['ssh', host, 'mkdir', '-p', '/home/amarshah'], check=True)
        
        # Copy each directory
        for directory in DIRECTORIES_TO_COPY:
            local_path = Path(directory)
            if not local_path.exists():
                logging.error(f"Directory {directory} does not exist locally")
                return False
                
            logging.info(f"Copying {directory} to {host}")
            
            # Build rsync command
            rsync_cmd = ['rsync', '-av']
            
            # Add compression flag based on user preference
            if use_compression:
                rsync_cmd.append('-z')
            else:
                rsync_cmd.append('--no-compress')
            
            # Add exclude patterns if specified
            if exclude_patterns:
                for pattern in exclude_patterns:
                    rsync_cmd.extend(['--exclude', pattern])
            
            # Add source and destination
            rsync_cmd.extend([
                str(local_path),
                f'{host}:/home/amarshah/'
            ])
            
            subprocess.run(rsync_cmd, check=True)
            
        return True
    except subprocess.CalledProcessError as e:
        logging.error(f"Failed to copy directories to {host}: {e}")
        return False

def setup_remote_environment(host: str) -> bool:
    """Set up the remote environment by building necessary components."""
    try:
        # # Build CaDiCaL
        # logging.info(f"Building CaDiCaL on {host}...")
        # result = subprocess.run([
        #     'ssh', host,
        #     'cd', '/home/amarshah/cadical', '&&',
        #     'rm', '-rf', 'build', '&&',
        #     'mkdir', '-p', 'build', '&&',
        #     'cd', 'build', '&&',
        #     '../configure', '&&',
        #     'make'
        # ], capture_output=True, text=True)
        
        # if result.returncode != 0:
        #     logging.error(f"CaDiCaL build failed on {host}:")
        #     logging.error(f"stdout: {result.stdout}")
        #     logging.error(f"stderr: {result.stderr}")
        #     return False
        
        # Build CautiCaL
        logging.info(f"Building CautiCaL on {host}...")
        result = subprocess.run([
            'ssh', host,
            'cd', '/home/amarshah/cautical', '&&',
            'rm', '-rf', 'build', '&&',
            'mkdir', '-p', 'build', '&&',
            'cd', 'build', '&&',
            '../configure', '&&',
            'make'
        ], capture_output=True, text=True)
        
        if result.returncode != 0:
            logging.error(f"CautiCaL build failed on {host}:")
            logging.error(f"stdout: {result.stdout}")
            logging.error(f"stderr: {result.stderr}")
            return False
        
        # Build dpr-trim
        logging.info(f"Building dpr-trim on {host}...")
        result = subprocess.run([
            'ssh', host,
            'cd', '/home/amarshah/dpr-trim', '&&',
            'make', 'clean', '&&',
            'make'
        ], capture_output=True, text=True)
        
        if result.returncode != 0:
            logging.error(f"dpr-trim build failed on {host}:")
            logging.error(f"stdout: {result.stdout}")
            logging.error(f"stderr: {result.stderr}")
            return False
        
        return True
    except subprocess.CalledProcessError as e:
        logging.error(f"Failed to set up environment on {host}: {e}")
        if hasattr(e, 'output'):
            logging.error(f"Command output: {e.output}")
        if hasattr(e, 'stderr'):
            logging.error(f"Command stderr: {e.stderr}")
        return False

def distribute_workload(args: argparse.Namespace) -> List[Dict[str, Any]]:
    """Distribute the workload across all remote hosts."""
    # Get all input files
    input_folder = Path(args.folder)
    input_files = list(input_folder.glob("*.cnf"))
    
    # Create output directory
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    output_dir = Path(f"results_{timestamp}")
    output_dir.mkdir(exist_ok=True)
    
    # Create proof directory if needed
    if args.produce_proofs:
        proof_dir = Path("proofs") #output_dir / "proofs"
        proof_dir.mkdir(exist_ok=True)
    
    # Statistics tracking
    sat_times = []
    unsat_times = []
    sat_count = 0
    unsat_count = 0
    timeout_count = 0
    error_count = 0
    
    # Open output file
    output_file = output_dir / f"results_{timestamp}.txt"
    with open(output_file, "w") as f:
        start_time = datetime.datetime.now()
        f.write(f"Experiment started at: {start_time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Input folder: {args.folder}\n")
        f.write(f"Solver: {args.solver}\n")
        f.write(f"Timeout: {args.timeout}s\n")
        if args.solver == "prelearn":
            f.write(f"PReLearn timeout: {args.prelearn_timeout}s\n")
        f.write(f"Produce proofs: {args.produce_proofs}\n")
        f.write(f"Check proofs: {args.check_proofs}\n")
        f.write(f"Number of instances: {len(input_files)}\n")
        f.write("-" * 80 + "\n")
        
        # Create a thread pool for each host
        host_pools = {}
        for host, cores in REMOTE_HOSTS.items():
            host_pools[host] = concurrent.futures.ThreadPoolExecutor(max_workers=cores)
        
        # Distribute files among hosts
        futures = []
        for i, file_path in enumerate(input_files):
            host = list(REMOTE_HOSTS.keys())[i % len(REMOTE_HOSTS)]
            pool = host_pools[host]
            
            # Create proof path if needed
            proof_path = None
            if args.produce_proofs:
                proof_path = proof_dir / f"{file_path.stem}.pr"
                absolute_proof_path = proof_path.absolute()
            
            # Submit job to host's thread pool
            future = pool.submit(
                run_cadical,
                file_path,
                absolute_proof_path,
                args.timeout,
                args.produce_proofs,
                args.check_proofs,
                args.solver,
                args.prelearn_timeout,
                host  # Pass host information
            )
            futures.append((future, host))  # Store host with future
        
        # Process results as they complete
        for future, host in futures:
            result = future.result()
            
            # Print solving result immediately with host information
            solving_output = f"{result['file_name']} [{host}]: {result['status']} ({result['runtime']:.2f}s)"
            if args.solver == "prelearn" and result['phase1_time'] is not None and result['phase2_time'] is not None:
                solving_output += f" [PReLearn: {result['phase1_time']:.2f}s, CaDiCaL: {result['phase2_time']:.2f}s]"
            print(solving_output)
            f.write(solving_output + "\n")
            
            # Print assignment if SAT
            if result['status'] == "SAT" and result['assignment']:
                print(result['assignment'])
                f.write(' '.join(result['assignment']) + "\n")
            
            # Print verification result separately if available
            if args.check_proofs and result['proof_status']:
                verify_output = f"{result['file_name']} [{host}]: Proof {result['proof_status']} ({result['proof_time']:.2f}s)"
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
        
        # Shutdown all thread pools
        for pool in host_pools.values():
            pool.shutdown()
        
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
    
    return []

def run_cadical(file_path: Path, proof_path: Path, timeout: int, produce_proofs: bool, 
               check_proofs: bool, solver: str, prelearn_timeout: int, host: str) -> Dict[str, Any]:
    """Run CaDiCaL on a single file and return the results."""
    start_time = time.time()
    try:
        # Create tmp directory on remote host
        subprocess.run(['ssh', host, 'mkdir', '-p', '/home/amarshah/tmp'], check=True)
        
        # Copy input file to remote host
        remote_file_path = f"/home/amarshah/tmp/{file_path.name}"
        subprocess.run(['scp', str(file_path), f'{host}:{remote_file_path}'], check=True)
        
        if solver == "prelearn":
            # Create prelearn directory on remote host
            subprocess.run(['ssh', host, 'mkdir', '-p', f'/home/amarshah/prelearn/{file_path.stem}'], check=True)
            
            # Phase 1: Run PReLearn
            phase1_start = time.time()
            phase1_cmd = f"cd /home/amarshah/prelearn/{file_path.stem} && /home/amarshah/PReLearn/PReLearn/sadical --pre_iterations=50 {remote_file_path}"
            try:
                print(f"[{host}] Starting PReLearn phase for {file_path.name}")
                phase1_result = subprocess.run(
                    ['ssh', host, phase1_cmd],
                    capture_output=True,
                    text=True,
                    timeout=prelearn_timeout
                )
                phase1_time = time.time() - phase1_start
                
                if phase1_result.returncode != 0:
                    print("PReLearn failed")
                    subprocess.run(['ssh', host, f'rm -rf /home/amarshah/prelearn/{file_path.stem}'], check=True)
                    return {
                        "file_name": file_path.name,
                        "status": "ERR: PReLearn failed",
                        "runtime": phase1_time,
                        "phase1_time": phase1_time,
                        "phase2_time": 0,
                        "proof_status": None,
                        "proof_time": None,
                        "assignment": None,
                        "host": host
                    }
            except subprocess.TimeoutExpired:
                phase1_time = prelearn_timeout
                combined_path = remote_file_path
            
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
                pr_clauses_path = f"/home/amarshah/prelearn/{file_path.stem}/pr_clauses.cnf"
                pr_lines = subprocess.run(
                    ['ssh', host, f'cat {pr_clauses_path}'],
                    capture_output=True,
                    text=True
                ).stdout.split('\n')
                pr_lines = [line for line in pr_lines if not line.startswith('c') and line.strip()]
                num_pr_clauses = len(pr_lines)
                
                # Create combined file
                combined_path = f"/home/amarshah/prelearn/{file_path.stem}/{file_path.stem}_with_pr.cnf"
                
                # Write modified header and clauses
                header_cmd = f"echo 'p cnf {num_vars} {num_clauses + num_pr_clauses}' > {combined_path}"
                subprocess.run(['ssh', host, header_cmd], check=True)
                
                # Write original clauses
                with open(file_path, 'r') as in_f:
                    for line in in_f:
                        if not line.startswith('p cnf'):
                            subprocess.run(['ssh', host, f'echo "{line.strip()}" >> {combined_path}'], check=True)
                
                # Write PR clauses
                for line in pr_lines:
                    subprocess.run(['ssh', host, f'echo "{line.strip()}" >> {combined_path}'], check=True)
            
            # Phase 2: Run CaDiCaL on combined file
            phase2_start = time.time()
            phase2_cmd = f"cd /home/amarshah/prelearn/{file_path.stem} && /home/amarshah/cadical/build/cadical {combined_path}"
            if produce_proofs:
                phase2_cmd += f" {proof_path}"
            
            print(f"[{host}] Starting CaDiCaL phase for {file_path.name}")
            phase2_result = subprocess.run(
                ['ssh', host, phase2_cmd],
                capture_output=True,
                text=True,
                timeout=timeout
            )
            phase2_time = time.time() - phase2_start
            
            # Determine result and capture assignment if SAT
            assignment = []
            if phase2_result.returncode == 10:
                status = "SAT"
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
            subprocess.run(['ssh', host, f'rm -rf /home/amarshah/prelearn/{file_path.stem}'], check=True)
            
            return {
                "file_name": file_path.name,
                "status": status,
                "runtime": phase1_time + phase2_time,
                "phase1_time": phase1_time,
                "phase2_time": phase2_time,
                "proof_status": None,  # PReLearn proofs are not verified
                "proof_time": None,
                "assignment": assignment,
                "host": host
            }
            
        else:  # cautical or cadical
            # Run CaDiCaL
            if solver == "cautical":
                cmd = f"cd /home/amarshah/cautical && CADICAL_FILENAME=l.t ./build/cadical --globalpreprocess {remote_file_path}"
            else:  # cadical
                cmd = f"cd /home/amarshah/cadical && ./build/cadical {remote_file_path}"
            
            if produce_proofs:
                cmd += f" {proof_path}"
            
            print(f"[{host}] Starting {solver} for {file_path.name}")
            result = subprocess.run(
                ['ssh', host, cmd],
                capture_output=True,
                text=True,
                timeout=timeout
            )
            
            # Determine result and capture assignment if SAT
            assignment = []
            if result.returncode == 10:
                status = "SAT"
                lines = result.stdout.split('\n')[-1000:]
                for line in lines:
                    if line.startswith('v '):
                        assignment += line.split(" ")[1:]
            elif result.returncode == 20:
                status = "UNSAT"
            else:
                status = f"ERR: {result.returncode}"
                print(cmd)
                print(result.stdout)
                print(result.stderr)
                
            runtime = time.time() - start_time
            
            # Verify proof if requested
            proof_status = None
            proof_time = None
            if check_proofs and result.returncode == 20:  # Only verify UNSAT proofs
                try:
                    print(f"[{host}] Starting proof verification for {file_path.name}")
                    verify_start = time.time()
                    verify_cmd = f"cd /home/amarshah/dpr-trim && ./dpr-trim {remote_file_path} {proof_path}"
                    verify_result = subprocess.run(
                        ['ssh', host, verify_cmd],
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
                "assignment": assignment,
                "host": host
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
            "assignment": None,
            "host": host
        }
    finally:
        # Clean up files
        subprocess.run(['ssh', host, f'rm -f {remote_file_path}'], check=True)
        if produce_proofs:
            subprocess.run(['ssh', host, f'rm -f {proof_path}'], check=True)

def main():
    parser = argparse.ArgumentParser(description="Run distributed CaDiCaL experiments")
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
    parser.add_argument("--solver", choices=["cautical", "cadical", "prelearn"], default="cautical",
                      help="Solver to use")
    parser.add_argument("--skip_setup", action="store_true",
                      help="Skip copying files and setting up remote machines")
    parser.add_argument("--compress", action="store_true",
                      help="Use compression during file transfer (slower but uses less bandwidth)")
    parser.add_argument("--exclude", nargs='+', default=['.git', '*.o', '*.a', '*.so', '*.dylib', '*.dll', '*.exe'],
                      help="Patterns to exclude during file transfer")
    
    args = parser.parse_args()
    
    # Validate arguments
    if args.check_proofs and not args.produce_proofs:
        parser.error("--check_proofs requires --produce_proofs")
    
    # Copy files and set up remote machines if not skipped
    if not args.skip_setup:
        logging.info("Copying files to remote machines...")
        for host in REMOTE_HOSTS:
            # if not copy_directories_to_remote(host, args.compress, args.exclude):
            #     logging.error(f"Failed to copy files to {host}")
            #     sys.exit(1)
            
            logging.info(f"Setting up environment on {host}...")
            if not setup_remote_environment(host):
                logging.error(f"Failed to set up environment on {host}")
                sys.exit(1)
    
    # Distribute workload and collect results
    logging.info("Distributing workload...")
    results = distribute_workload(args)
    
    # Write final results
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    final_output_file = f"results/final_results_{timestamp}.json"
    with open(final_output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    logging.info(f"Results written to {final_output_file}")

if __name__ == "__main__":
    main() 