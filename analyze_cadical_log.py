#!/usr/bin/env python3
import argparse
import statistics
import re
import pandas as pd
from collections import defaultdict

def load_prelearn_times():
    """Load prelearn times and original times from both CSV files"""
    df2023 = pd.read_csv('results2023.csv')
    df2024 = pd.read_csv('results2024.csv')
    # Create dictionaries mapping filenames to times
    prelearn_times = {}
    original_times = {}
    # First add 2023 data
    for _, row in df2023.iterrows():
        prelearn_times[row['file_name']] = row['median_time_prelearn']
        original_times[row['file_name']] = row['original_time']
    # Then add 2024 data for any files not in 2023
    for _, row in df2024.iterrows():
        if row['file_name'] not in prelearn_times:
            prelearn_times[row['file_name']] = row['median_time_prelearn']
            original_times[row['file_name']] = row['original_time']
    return prelearn_times, original_times

def parse_line(line):
    """
    Extracts:
    - status (SAT/UNSAT/etc.)
    - file name
    - rep number
    - time in seconds
    - full command
    """
    match = re.match(
        r"\[(\w+)\s*\] (\S+)\s+(base|orderi) rep(\d+)\s+([\d.]+)s\s+\|\s+(.*)", line)
    if not match:
        return None
    status, filename, variant, rep, time_sec, command = match.groups()
    return {
        "status": status,
        "file": filename,
        "variant": variant,
        "rep": int(rep),
        "time": float(time_sec),
        "command": command.strip()
    }

def summarize(times):
    if not times:
        return {"mean": None, "median": None, "min": None, "max": None}
    return {
        "mean": round(statistics.mean(times), 2),
        "median": round(statistics.median(times), 2),
        "min": round(min(times), 2),
        "max": round(max(times), 2)
    }

def analyze_log(file_path, options):
    # Load prelearn times and original times
    prelearn_times, original_times = load_prelearn_times()
    
    with open(file_path, "r") as f:
        lines = f.readlines()

    option_keys = [f"{opt}" for opt in options]
    grouped = defaultdict(lambda: {key: [] for key in option_keys + ["neither"]})

    for line in lines:
        parsed = parse_line(line)
        if not parsed:
            continue

        cmd = parsed["command"]
        matched = False
        for opt in options:
            if opt in cmd:
                grouped[parsed["file"]][opt].append(parsed["time"])
                matched = True

        if not matched:
            grouped[parsed["file"]]["neither"].append(parsed["time"])

    print(f"\nTiming comparison (each option treated independently)\n")

    # Dynamically determine padding for query column
    max_query_len = max(len(fname) for fname in grouped.keys())
    query_col_width = min(max_query_len + 2, 70)  # cap to avoid overexpanding

    # Column config
    stat_col_width = 10
    header = ["Query"] + [f"{opt}" for opt in options] + ["Neither", "Prelearn", "Original"]
    header_fmt = f"{{:<{query_col_width}}} | " + " | ".join(
        [f"{{:<{stat_col_width}}}"] * (len(header) - 1)
    )
    row_fmt = f"{{:<{query_col_width}}} | " + " | ".join(
        [f"med={{:<{stat_col_width}}}"] * (len(header) - 3) + [f"{{:<{stat_col_width}}}"] * 2
    )

    print(header_fmt.format(*header))
    print("-" * (query_col_width + 3 + (stat_col_width + 3) * (len(header) - 1)))

    for file, data in grouped.items():
        stat_list = []
        for key in options + ["neither"]:
            s = summarize(data[key])
            stat_list.extend([
                str(s["median"]),
            ])
        # Add prelearn time if available, otherwise "N/A"
        prelearn_time = prelearn_times.get(file, "N/A")
        if prelearn_time != "N/A":
            prelearn_time = prelearn_time + 30
            prelearn_time = f"{prelearn_time:.2f}"
        stat_list.append(prelearn_time)
        
        # Add original time if available, otherwise "N/A"
        original_time = original_times.get(file, "N/A")
        if original_time != "N/A":
            original_time = f"{original_time:.2f}"
        stat_list.append(original_time)
        
        print(row_fmt.format(file, *stat_list))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Compare CaDiCaL timing for multiple options")
    parser.add_argument("logfile", help="Path to log file")
    parser.add_argument("options", nargs="+", help="One or more command-line options to analyze")
    args = parser.parse_args()

    analyze_log(args.logfile, args.options)

