"""Numerical check of the graph-state AME criterion that the Lean proof formalises.

The state of a graph Gamma over Z_d on n parties is
    psi(x) = d^(-n/2) * w^(sum_{i<j} Gamma_ij x_i x_j + sum_i Gamma_ii x_i^2),  w = exp(2 pi i/d).
Claim: every reduction to n/2 parties is I/d^(n/2) when every block Gamma[A, complement of A] is
invertible mod d. The 12-party state is too large to build (5^12 amplitudes), so this checks
the claim on random 6-party graphs over Z_5: one whose blocks are all invertible must be AME,
and one with a singular block must not be.

Needs numpy. Exits 1 if either check fails.
"""
import itertools
import random
import sys

import numpy as np

D, N, H = 5, 6, 3
CUTS = list(itertools.combinations(range(N), H))


def rank_mod(m):
    m = [row[:] for row in m]
    r = 0
    for c in range(len(m[0])):
        piv = next((i for i in range(r, len(m)) if m[i][c] % D), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = pow(m[r][c], D - 2, D)
        m[r] = [x * inv % D for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] % D:
                f = m[i][c]
                m[i] = [(a - f * b) % D for a, b in zip(m[i], m[r])]
        r += 1
    return r


def blocks_ok(g):
    return all(rank_mod([[g[i][j] for j in range(N) if j not in a] for i in a]) == H
               for a in CUTS)


def state(g):
    w = np.exp(2j * np.pi / D)
    psi = np.zeros([D] * N, dtype=complex)
    for x in itertools.product(range(D), repeat=N):
        q = (sum(g[i][j] * x[i] * x[j] for i in range(N) for j in range(i + 1, N))
             + sum(g[i][i] * x[i] * x[i] for i in range(N)))
        psi[x] = w ** (q % D)
    return psi / D ** (N / 2)


def worst_deviation(psi):
    worst = 0.0
    for a in CUTS:
        b = [j for j in range(N) if j not in a]
        m = np.transpose(psi, list(a) + b).reshape(D ** H, D ** H)
        worst = max(worst, np.abs(m @ m.conj().T - np.eye(D ** H) / D ** H).max())
    return worst


random.seed(3)
good = bad = None
while good is None or bad is None:
    g = [[0] * N for _ in range(N)]
    for i in range(N):
        for j in range(i, N):
            g[i][j] = g[j][i] = random.randrange(D)
    if blocks_ok(g):
        good = good or g
    else:
        bad = bad or g
dev_good, dev_bad = worst_deviation(state(good)), worst_deviation(state(bad))
print(f"all blocks invertible: max |rho - I/{D ** H}| over {len(CUTS)} cuts = {dev_good:.2e}")
print(f"a singular block:      max |rho - I/{D ** H}| = {dev_bad:.2e}")
ok = dev_good < 1e-12 and dev_bad > 1e-6
print("RESULT:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
