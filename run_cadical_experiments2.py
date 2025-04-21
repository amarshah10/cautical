#!/usr/bin/env python3
"""
run_cadical_experiments.py
Run CaDiCaL on every file in a target folder under every combination
of four flag‑families (plus an optional “globalorderi=true”) and
summarise the results.

Usage
-----
    python run_cadical_experiments.py  [-j N]  [--out results.csv]
                                       [sat_folder]

    -j / --jobs N     maximum parallel jobs   (default: #logical CPUs)
    --out  FILE       CSV file for final log  (default: results.csv)
    sat_folder        folder holding *.cnf / *.smt2  (default:
                       "satcomp_benchmarks_target")
"""

import argparse
import csv
import itertools
import os
import pathlib
import shlex
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

###############################################################################
# 1. flag definitions
###############################################################################
FILTER_TRIV_OPTS = [
    "--globalfiltertriv=false",
    "--globalfiltertriv=true",
    "--globalfiltertriv=true --globalmaxlen=2",
    "--globalfiltertriv=true --globalmaxlen=4",
    "--globalfiltertriv=true --globalmaxlen=8",
    "--globalfiltertriv=true --globalmaxlen=16",
]

PREPROC_TIME_OPTS = [
    "--globaltimelim=5",
    "--globaltimelim=30",
    "--globaltimelim=120",
]

# BCP_OPTS = [
#     "--globalbcp=true",
#     "--globalbcp=false",
# ]

# TOUCH_OPTS = [
#     "--globaltouch=true",
#     "--globaltouch=false",
# ]

ALPHA_ORDER_OPTIONS = [
    "--globalalphaasort=true",
    "--globalalphaarandom=true",
    "",
]

ALPHA_GREEDY_OPTIONS = [
    "--globalalphaagreedy=true",
    ""
]


BASE_CMD = (
    "build/cadical "
    "--report=true --chrono=false "
    "--global=true "
    "--globalpreprocess=true "
    "--globalbcp=false "
    "--globaltouch=true "
    "--globalrecord=false "
)

TIMEOUT_SEC = 300
REPETITIONS = 10           # per option set w/o globalorderi
ORDERI_REPETITIONS = 1     # per option set with globalorderi=true
###############################################################################


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="CaDiCaL massive runner")
    parser.add_argument("folder", nargs="?", default="satcomp_benchmarks_target")
    parser.add_argument("-j", "--jobs", type=int, default=os.cpu_count())
    parser.add_argument("--out", default="results.csv",
                        help="CSV file to save all results (append‑mode)")
    return parser.parse_args()


def build_option_sets():
    """Return the 72 combo strings plus the 72 '+orderi' variants."""
    combos = list(
        " ".join(parts)
        for parts in itertools.product(
            FILTER_TRIV_OPTS,
            PREPROC_TIME_OPTS,
            ALPHA_ORDER_OPTIONS,
            ALPHA_GREEDY_OPTIONS,
        )
    )
    with_orderi = [f"{c} --globalorderi=true" for c in combos]
    return combos, with_orderi


def classify_exit(returncode: int) -> str:
    if returncode == 10:
        return "SAT"
    if returncode == 20:
        return "UNSAT"
    return f"ERR({returncode})"


def run_once(cmd: str, env: dict) -> str:
    """Run a single command, return status str."""
    start = time.perf_counter()
    try:
        completed = subprocess.run(
            shlex.split(cmd),
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=TIMEOUT_SEC,
        )
        status = classify_exit(completed.returncode)
    except subprocess.TimeoutExpired:
        status = "TIMEOUT"
    duration = f"{time.perf_counter() - start:.2f}"
    return status, duration


def job(file_path: pathlib.Path, opt_string: str, rep: int, with_orderi: bool):
    """Callable for the executor pool."""
    env = os.environ.copy()
    env["CADICAL_FILENAME"] = str(file_path)[-15:]

    full_cmd = f"{BASE_CMD} {opt_string} {shlex.quote(str(file_path))}"
    status, secs = run_once(full_cmd, env)

    record = {
        "file": str(file_path),
        "options": opt_string,
        "orderi": with_orderi,
        "rep": rep,
        "status": status,
        "seconds": secs,
        "cmd": full_cmd,
    }
    # Echo progress so we don't lose everything if interrupted
    start_pos = 150
    max_len = 140 + start_pos                         # adjust to taste
    cmd_disp = (full_cmd[start_pos: max_len - 1] + "…") if len(full_cmd) > max_len else full_cmd

    print(
        f"[{record['status']:<8}] "
        f"{file_path.name:<35} "
        f"{'orderi' if with_orderi else 'base'} "
        f"rep{rep:<2} "
        f"{secs}s  |  {cmd_disp}"
    )
    # If error code, show command for debugging
    if record["status"].startswith("ERR"):
        print("   ↳ cmd:", full_cmd, file=sys.stderr)

    return record


def main():
    args = parse_args()
    target_dir = pathlib.Path(args.folder).expanduser().resolve()
    if not target_dir.is_dir():
        sys.exit(f"folder '{target_dir}' does not exist or is not a directory")

    combos, combos_orderi = build_option_sets()

    # Gather every regular file
    files = sorted(p for p in target_dir.iterdir() if p.is_file())
    if not files:
        sys.exit(f"No files found in {target_dir}")

    print(
        f"Running on {len(files)} files  |  "
        f"{len(combos)} base combos x {REPETITIONS} reps  +  "
        f"{len(combos_orderi)} orderi combos x {ORDERI_REPETITIONS} reps"
    )

    all_records = []
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futures = []

        # Base combos
        for path in files:
            for opt in combos:
                for r in range(1, REPETITIONS + 1):
                    futures.append(
                        ex.submit(job, path, opt, r, False)
                    )

        # Combos with globalorderi=true
        for path in files:
            for opt in combos_orderi:
                for r in range(1, ORDERI_REPETITIONS + 1):
                    futures.append(
                        ex.submit(job, path, opt, r, True)
                    )

        for fut in as_completed(futures):
            all_records.append(fut.result())

    # Persist results
    header = [
        "file",
        "options",
        "orderi",
        "rep",
        "status",
        "seconds",
        "cmd",
    ]
    out_file = pathlib.Path(args.out)
    write_header = not out_file.exists()
    with out_file.open("a", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=header)
        if write_header:
            writer.writeheader()
        writer.writerows(all_records)

    print("\nFinished. Results saved to", out_file)


if __name__ == "__main__":
    main()
