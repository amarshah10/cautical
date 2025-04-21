import os
import shutil

# Target directory
target_dir = "satcomp_benchmarks_target"
os.makedirs(target_dir, exist_ok=True)

# Source directories and file names
sources = {
    "satcomp_benchmarks": [
        "8704094951693f99fd21403a039c8131-mchess_16.cnf",
        "ec84eecb124c63d4757e083dd0e5a9ff-mchess_15.cnf",
        "2c3c28f6d939d157e909c57a265fc908-mchess_17.cnf",
        "cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf"
    ],
    "satcomp_benchmarks23": [
        "44092fcc83a5cba81419e82cfd18602c-php-010-009.shuffled-as.sat05-1185.cnf",
        "246afd75cb97a21144f368c00252a656-BZ2File_write_11.cnf",
        "112b0ac22b2a567cd3badfed3a5497fd-mchess16-mixed-35percent-blocked.cnf",
        "ff867fd35aa52058382a8b0c21cd1f38-mchess20-mixed-35percent-blocked.cnf",
        "b09585f2346c207e9e14a3daf0de46cf-CNF_to_alien_11.cnf",
        "21bde0ebb111c637a1ae8789827b0b73-WCNF_from_fp_13.cnf",
        "37d40a1092b58ad28285b9453872d211-DecompressReader_read_12.cnf",
        "41a8365f60db55b71d949df6954e0db7-FileObject_open_13.cnf",
        "11db226d109e82f93aaa3b2604173ff9-posixpath__joinrealpath_13.cnf",
        "c32f194ad850c944142c74514dfb3c5f-WCNFPlus_from_fp_13.cnf",
        "a4b05fbc5be28207b704e1fae4b7c8a0-FileObject_open_12.cnf",
        "72b5ad031bf852634bc081f9da9a5a60-GzipFile_close_11.cnf",
        "4029fbae284eaf924b37b6f43d3a67fb-WCNF_from_fp_14.cnf",
        "fd2af7622798171f23a4b8d2616df55e-StreamReader_readline_13.cnf",
        "6aacae96461cb65176942b6dc88ea470-mchess20-mixed-25percent-blocked.cnf",
        "7aaf3275cbe217044ef305f0a1ca8eb5-CNFPlus_from_fp_12.cnf",
        "965ca988015c9aee5a1a7b2136c1fe5d-os_fwalk_12.cnf",
        "19004c7d629f7e6e83c6e1d7a9a768a9-6s166.cnf",
        "8d458780fb74c28c01a5fe89990ad521-mchess16-mixed-45percent-blocked.cnf",
        "d7f381cd99ca40ba3324c8cc03a54269-mchess16-mixed-25percent-blocked.cnf",
        "644fd765d26bd4a380922ccd0f594c58-mchess18-mixed-25percent-blocked.cnf",
        "fe8b1ef742724947620a419d0180a640-mchess18-mixed-35percent-blocked.cnf",
        "41457ee03686b32962c12445524f62a9-mchess18-mixed-45percent-blocked.cnf",
        "751afd7ddf8f242ed7bd93517ba82149-mchess20-mixed-45percent-blocked.cnf",
        "dd169198070f9aa35015de65e8209a05-LZMAFile_write_12.cnf",
        "824c21545e228872744675ae4ee32976-WCNFPlus_to_alien_14.cnf",
        "b2145c28dbed385329ea73a06d9c519a-LZMAFile___init___14.cnf",
        "af1e84bc2ab44d87d1c4c0cbf9e601c5-posixpath_expanduser_14.cnf"
    ]
}

# Use a set to deduplicate
copied_files = set()

for src_dir, file_list in sources.items():
    for filename in file_list:
        if filename in copied_files:
            continue  # Skip duplicates
        src_path = os.path.join(src_dir, filename)
        dst_path = os.path.join(target_dir, filename)
        if os.path.isfile(src_path):
            shutil.copy(src_path, dst_path)
            print(f"Copied: {src_path} → {dst_path}")
            copied_files.add(filename)
        else:
            print(f"Missing: {src_path} (not copied)")

print(f"\nFinished copying {len(copied_files)} files into '{target_dir}'.")
