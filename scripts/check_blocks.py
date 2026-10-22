"""Check that the graph matrix gives an AME(12,5) graph state, exactly, over Z_5.

A qudit graph state on n parties is AME when, for every set A of n/2 parties, the block
Gamma[A, complement of A] is invertible mod d. This script checks all 924 such blocks of the
matrix in data/theta_ame125.txt by exact Gaussian elimination mod 5. As a control it then
changes one off-diagonal entry and requires that some block becomes singular.

Exits 1 if any check fails.
"""
import itertools
import sys

P, N, H = 5, 12, 6


def load(path):
    rows = [list(map(int, line.split())) for line in open(path) if line.strip()]
    if len(rows) != N or any(len(r) != N for r in rows):
        sys.exit(f"{path}: expected a {N} x {N} matrix")
    if any(not 0 <= x < P for r in rows for x in r):
        sys.exit(f"{path}: entries must lie in 0..{P - 1}")
    return rows


def rank_mod(m):
    m = [row[:] for row in m]
    r = 0
    for c in range(len(m[0])):
        piv = next((i for i in range(r, len(m)) if m[i][c] % P), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = pow(m[r][c], P - 2, P)
        m[r] = [x * inv % P for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] % P:
                f = m[i][c]
                m[i] = [(a - f * b) % P for a, b in zip(m[i], m[r])]
        r += 1
    return r


def singular_cuts(g):
    bad = []
    for a in itertools.combinations(range(N), H):
        b = [j for j in range(N) if j not in a]
        if rank_mod([[g[i][j] for j in b] for i in a]) < H:
            bad.append(a)
    return bad


path = sys.argv[1] if len(sys.argv) > 1 else "data/theta_ame125.txt"
g = load(path)
ok = True
if any(g[i][j] != g[j][i] for i in range(N) for j in range(N)):
    print("FAIL: the matrix is not symmetric")
    ok = False
bad = singular_cuts(g)
print(f"balanced cuts checked: {len(list(itertools.combinations(range(N), H)))}; "
      f"singular blocks: {len(bad)}")
if bad:
    print("FAIL: singular blocks at", bad[:5])
    ok = False
control = [r[:] for r in g]
control[0][6] = control[6][0] = (control[0][6] + 1) % P
n_bad = len(singular_cuts(control))
print(f"control (entry (0,6) changed): singular blocks: {n_bad}")
if n_bad == 0:
    print("FAIL: the control did not break any block")
    ok = False
print("RESULT:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
