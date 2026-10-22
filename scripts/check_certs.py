"""Check the stored certificates the way the Lean kernel will.

Reads data/theta_ame125.txt and data/certs.txt. Requires the masks, in file order, to be
exactly the 924 twelve-bit masks with six bits set, in increasing order (`certs_masks` in
Lean), and for each certificate L that Gamma[A, B] * L = I mod 5, with A the set bits and B the
clear bits, both in increasing order (`certs_ok` in Lean).

Exits 1 if any check fails.
"""
import sys

P, N, H = 5, 12, 6
theta = sys.argv[1] if len(sys.argv) > 1 else "data/theta_ame125.txt"
certs = sys.argv[2] if len(sys.argv) > 2 else "data/certs.txt"
g = [list(map(int, line.split())) for line in open(theta) if line.strip()]
entries = []
for line in open(certs):
    if not line.strip():
        continue
    nums = list(map(int, line.split()))
    if len(nums) != 1 + H * H:
        sys.exit(f"bad line: {line.strip()[:40]}")
    entries.append((nums[0], [nums[1 + H * i:1 + H * (i + 1)] for i in range(H)]))
want = [m for m in range(1 << N) if bin(m).count("1") == H]
ok = [mask for mask, _ in entries] == want
if not ok:
    print("FAIL: the masks are not exactly the six-bit masks in increasing order")
for mask, left in entries:
    a = [i for i in range(N) if mask >> i & 1]
    b = [j for j in range(N) if not mask >> j & 1]
    m = [[g[i][j] for j in b] for i in a]
    prod = [[sum(m[i][t] * left[t][j] for t in range(H)) % P for j in range(H)] for i in range(H)]
    if prod != [[int(i == j) for j in range(H)] for i in range(H)]:
        print(f"FAIL: certificate for mask {mask} is not a right inverse of its block")
        ok = False
print(f"certificates: {len(entries)}, expected masks: {len(want)};",
      "RESULT: PASS" if ok else "RESULT: FAIL")
sys.exit(0 if ok else 1)
