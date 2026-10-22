"""Generate an inverse certificate for every balanced cut of the graph matrix.

For each set A of 6 parties out of 12 (as a 12-bit mask, bit i set when party i is in A) and
B its complement, both listed in increasing order, the block is M = Gamma[A, B] (rows A,
columns B). The certificate is the 6 x 6 matrix L over Z_5 with L * M = I and M * L = I (rows
follow B, columns follow A). It shows the block is injective, which is what the Lean proof
needs, and the kernel only has to multiply it out (it checks M * L = I).

Usage: python scripts/gen_certs.py data/theta_ame125.txt data/certs.txt
Each output line is the mask followed by the 36 entries of L, row by row, in increasing order
of mask. The script checks every certificate both ways before writing and exits 1 if any block
is singular.
"""
import itertools
import sys

P, N, H = 5, 12, 6


def inverse_mod(m):
    k = len(m)
    a = [row[:] + [1 if i == j else 0 for j in range(k)] for i, row in enumerate(m)]
    for c in range(k):
        piv = next((i for i in range(c, k) if a[i][c] % P), None)
        if piv is None:
            return None
        a[c], a[piv] = a[piv], a[c]
        inv = pow(a[c][c], P - 2, P)
        a[c] = [x * inv % P for x in a[c]]
        for i in range(k):
            if i != c and a[i][c] % P:
                f = a[i][c]
                a[i] = [(x - f * y) % P for x, y in zip(a[i], a[c])]
    return [row[k:] for row in a]


def mul(x, y):
    return [[sum(x[i][t] * y[t][j] for t in range(len(y))) % P for j in range(len(y[0]))]
            for i in range(len(x))]


src, dst = sys.argv[1], sys.argv[2]
g = [list(map(int, line.split())) for line in open(src) if line.strip()]
lines = []
for a in itertools.combinations(range(N), H):
    b = [j for j in range(N) if j not in a]
    m = [[g[i][j] for j in b] for i in a]
    left = inverse_mod(m)
    if left is None or mul(left, m) != [[int(i == j) for j in range(H)] for i in range(H)]:
        sys.exit(f"singular block for A = {a}")
    mask = sum(1 << i for i in a)
    if mul(m, left) != [[int(i == j) for j in range(H)] for i in range(H)]:
        sys.exit(f"certificate is not a right inverse for A = {a}")
    lines.append(" ".join(map(str, [mask] + [x for row in left for x in row])))
lines.sort(key=lambda line: int(line.split()[0]))
with open(dst, "w", newline="\n") as f:
    f.write("\n".join(lines) + "\n")
print(f"wrote {len(lines)} certificates to {dst}")
