# Source of `theta_ame125.txt`

The 12 × 12 graph matrix over Z_5 of the AME(12,5) state of Samuel Bevins and Yunus Bidav,
"Symmetry-guided constructions of absolutely maximally entangled states in five open cases",
arXiv:2608.05781 (v2, 10 Aug 2026). The reproducibility package titles the paper "Symmetry-guided
construction and exact certification of absolutely maximally entangled states".

Copied on 2026-10-21 from the authors' reproducibility package,
https://github.com/sjbevins/AME-paper-materials, file `data/theta_ame125.txt`, at commit
`3fd8edc5bfc505e512c7a0c6168f92b44019f142` (13 Oct 2026, 01:40 UTC). The file is byte for byte
the authors' (288 bytes, LF line endings, sha256
`969c79dca61f249b39f5df825f2a87a72dbd09a3623faace89da29f3f8a7f0bd`), and `audit/lexical.py`
checks that hash. It is used under the MIT licence; the authors' licence notice is in
`LICENSE-Bevins-Bidav.txt`, also byte for byte.

The authors construct a Hermitian self-dual MDS code [12,6,7] over GF(25) and obtain from it
an AME(12,5) stabilizer state; their package gives that state in graph form, as this matrix.
Entry (i, j) for i ≠ j is the edge weight between parties i and j. The diagonal holds local
phase terms, which no balanced cut uses; the matrix in the authors' own verifier
(`verification/verify_ame_12_5.py`) has a zero diagonal, which differs only by those local
phases. Only this matrix is used here. None of the authors' code is used or needed: every
property this project relies on is checked again from the matrix alone, by the scripts in
`scripts/` and by the Lean proof.

`certs.txt` is generated from this matrix by `scripts/gen_certs.py`. For each of the 924 sets A
of six parties (a 12-bit mask, in increasing order) it gives the 6 × 6 inverse L over Z_5 of the
block Γ[A, Aᶜ], so Γ[A, Aᶜ] · L = I and L · Γ[A, Aᶜ] = I. The Lean kernel checks the first.

Checks (`scripts/`):
- `check_blocks.py`: the matrix is symmetric and all 924 blocks Γ[A, Aᶜ] are invertible mod 5,
  by exact elimination; a control with one entry changed must break some block.
- `check_certs.py`: the masks are exactly the 924 six-bit masks in increasing order and each
  certificate satisfies Γ[A, Aᶜ] · L = I, the same checks the Lean kernel makes.
- `check_criterion.py`: numerically, on random six-party graphs over Z_5, all blocks invertible
  gives every three-party reduction equal to I/125, and a singular block does not.

Earlier formal proof: Kenta Kitamura's `KitaKen1/ame-11-10-lean` (commit `6b7d009a`,
22 Sep 2026) proves `ExistsAME 12 5` against Formal Conjectures' definitions
(`AMEProbe.QuinaryParent.existsAME_12_5` in `lean/QuinaryParent.lean`), from the same graph with
the diagonal set to zero and 924 cut certificates, as a step towards AME(11,10). This
repository was written independently of it.
