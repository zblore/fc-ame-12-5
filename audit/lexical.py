"""Audit, lexical checks: doc promises, placeholders, import hygiene, format, data fidelity.

Run from the repository root, or pass the root as the first argument. Exits 1 if it finds any
problem, so it can gate CI.
"""
import glob
import hashlib
import os
import re
import subprocess
import sys
import tempfile

root = sys.argv[1] if len(sys.argv) > 1 else "."
files = sorted(glob.glob(os.path.join(root, "AME125", "*.lean")))
files.append(os.path.join(root, "AME125.lean"))
fc_path = os.path.join(root, ".lake/packages/formal_conjectures/FormalConjectures",
                       "OpenQuantumProblems/35.lean")
fc = open(fc_path, encoding="utf-8").read()
# Read bytes, so CRLF line endings are seen rather than silently converted.
raw = {f: open(f, "rb").read() for f in files}
src = {f: b.decode("utf-8") for f, b in raw.items()}
# Modifiers in any order, so `private lemma`, `protected def` and `private noncomputable def`
# are seen too, and indented declarations as well as ones at column zero.
decl_re = (r"^[ \t]*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
           r"(?:def|lemma|theorem|abbrev|structure|inductive)\s+(\S+)")
declared = set(re.findall(decl_re, "\n".join(src.values()), re.M))
declared |= set(re.findall(decl_re, fc, re.M))
problems = []
# audit/Vacuity.lean skips some suffixes as Lean-generated (its `generated` list, `eq_<n>` and
# `match_<n>`), so no hand-written name may use them. The list is read from Vacuity.lean so the
# two cannot drift.
vacuity = open(os.path.join(root, "audit", "Vacuity.lean"), encoding="utf-8").read()
generated_block = re.search(r"let generated : List String :=\s*\[(.*?)\]", vacuity, re.S)
if generated_block is None:
    sys.exit("lexical audit: cannot find the `generated` list in audit/Vacuity.lean")
reserved = set(re.findall(r'"([^"]+)"', generated_block.group(1)))
if len(reserved) < 10:
    sys.exit(f"lexical audit: only {len(reserved)} reserved suffixes read from Vacuity.lean")
# As in Vacuity.lean, the listed suffixes and `eq_<n>` count only as the last component of a
# name, but `match_<n>` counts in any component.
for f, s in src.items():
    for name in re.findall(decl_re, s, re.M):
        parts = name.split(".")
        if (parts[-1] in reserved or re.fullmatch(r"eq_\d+", parts[-1])
                or any(re.fullmatch(r"match_\d+", p) for p in parts)):
            problems.append(f"{f}: `{name}` uses a suffix reserved for Lean-generated lemmas")
for f, t in src.items():
    for doc in re.findall(r"/-[-!](.*?)-/", t, re.S):
        for name in re.findall(r"`([A-Za-z_][A-Za-z0-9_'.]*)`", doc):
            short = name.split(".")[-1]
            wordlike = "_" in short or short[:1].islower()
            # Qualified names such as `Finset.prod_add` or `lp.evalCLM` are taken to be
            # Mathlib's and are not checked, so a mistyped one would pass. Names here or in the
            # FC file are checked.
            qualified = ("." in name and name[:1].isupper()
                         and not name.startswith(("AME125.", "OpenQuantumProblem35.")))
            # Lean and Mathlib names used in prose, not declarations to check.
            known = {"sorry", "star", "linear_combination", "decide"}
            if (len(short) > 2 and short not in known and wordlike
                    and short not in declared and not qualified):
                problems.append(f"{f}: docstring names `{name}`, "
                                "not declared here or in the FC file")
    code = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", t, flags=re.S))
    if re.search(r":=\s*True\b|\bsorry\b|\badmit\b|native_decide", code):
        problems.append(f"{f}: placeholder, sorry, admit or native_decide")
    for imp in re.findall(r"^import\s+(\S+)", t, re.M):
        if not (imp.startswith("AME125") or imp == "Mathlib"
                or imp == "FormalConjectures.OpenQuantumProblems.«35»"):
            problems.append(f"{f}: imports {imp}")
    for i, line in enumerate(t.replace("\r\n", "\n").split("\n"), 1):
        if len(line) > 100:
            problems.append(f"{f}:{i}: {len(line)} characters")
        if line != line.rstrip():
            problems.append(f"{f}:{i}: trailing whitespace")
    if b"\r" in raw[f]:
        problems.append(f"{f}: CRLF line endings")
# Provenance: data/theta_ame125.txt must be byte for byte the authors' file at commit
# 3fd8edc5bfc505e512c7a0c6168f92b44019f142 of github.com/sjbevins/AME-paper-materials.
AUTHORS_SHA256 = "969c79dca61f249b39f5df825f2a87a72dbd09a3623faace89da29f3f8a7f0bd"
theta_path = os.path.join(root, "data", "theta_ame125.txt")
if hashlib.sha256(open(theta_path, "rb").read()).hexdigest() != AUTHORS_SHA256:
    problems.append(f"{theta_path} is not byte for byte the authors' file (sha256 differs)")
# Data fidelity: data/certs.txt must be exactly what scripts/gen_certs.py produces from the
# authors' matrix, and AME125/Data.lean exactly what scripts/gen_lean_data.py produces from the
# matrix and the certificates.
with tempfile.TemporaryDirectory() as tmp:
    certs_regen = os.path.join(tmp, "certs.txt")
    gen = subprocess.run([sys.executable, os.path.join(root, "scripts", "gen_certs.py"),
                          os.path.join(root, "data", "theta_ame125.txt"), certs_regen],
                         capture_output=True, text=True)
    certs_file = os.path.join(root, "data", "certs.txt")
    if gen.returncode != 0:
        problems.append("scripts/gen_certs.py rejects data/theta_ame125.txt: "
                        + (gen.stderr or gen.stdout).strip().splitlines()[-1])
    elif open(certs_regen, "rb").read() != open(certs_file, "rb").read():
        problems.append(f"{certs_file} differs from the certificates generated from the matrix")
    data_regen = os.path.join(tmp, "Data.lean")
    subprocess.run([sys.executable, os.path.join(root, "scripts", "gen_lean_data.py"),
                    os.path.join(root, "data", "theta_ame125.txt"), certs_file, data_regen],
                   check=True, capture_output=True)
    data_file = os.path.join(root, "AME125", "Data.lean")
    if open(data_regen, "rb").read() != raw[data_file]:
        problems.append(f"{data_file} differs from the file generated from the data")
if problems:
    print("\n".join(problems))
    sys.exit(1)
print(f"lexical audit clean over {len(files)} files")
