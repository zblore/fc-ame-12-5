# AME(12,5) in Lean

A Lean 4 proof that an absolutely maximally entangled state of twelve five-level systems exists. It proves `ame_12_5_open` from Open Quantum Problem 35 in Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) against their own definitions.

## The result

An AME(12,5) state is a state of twelve parties, each with five levels, where any six of them on their own look completely random. Samuel Bevins and Yunus Bidav found one: "Symmetry-guided constructions of absolutely maximally entangled states in five open cases", arXiv:2608.05781. They build a special error-correcting code over the field with 25 elements and turn it into a "graph state" over the numbers mod 5. Their [reproducibility package](https://github.com/sjbevins/AME-paper-materials) publishes the graph as a 12 × 12 table of numbers mod 5, under the MIT licence. That table is the witness here, used exactly as published. Its diagonal holds local phases; the authors' own verifier uses a zero diagonal, which changes nothing about entanglement. `data/SOURCE.md` says where it came from.

This isn't the first Lean proof. Kenta Kitamura proved the same statement on 22 Sep 2026, from the same graph, as a step in his [AME(11,10) proof](https://github.com/KitaKen1/ame-11-10-lean) (`existsAME_12_5` in `lean/QuinaryParent.lean`). I wrote this one independently before finding his. What it adds is a standalone proof of Formal Conjectures' current statement, a graph-state criterion that holds for any even number of parties and any table, and audits that tie the Lean data to the authors' published file.

## The proof

A graph state is AME when, for every way of splitting the twelve parties into two groups of six, the 6 × 6 block of the table between the two groups is invertible mod 5. So the proof is one general theorem, which is proved, and 924 small facts, which are computed.

Proved:

- `AME125/GraphState.lean` defines the graph state of any table U mod 5 on n parties: every amplitude is 5^(-n/2) times exp(2πi xᵀUx/5), so 5⁻⁶ for twelve parties. It proves the state is normalised when n is even, that reordering the parties gives the graph state of the reordered table, and that each reduction to half the parties is a character sum that comes out maximally mixed exactly when no non-zero vector on the kept half is killed by the block of U + Uᵀ between the two halves. That gives `graphState_isAME`: if every half-split block of U + Uᵀ is injective, the state is AME in Formal Conjectures' sense. It holds for any even number of parties and any table, so it isn't tied to this case. Here U is the upper triangle of the authors' table, so U + Uᵀ is their table off the diagonal.
- `AME125/Certificate.lean` turns "every block has an inverse" into "every set of six parties satisfies the condition", for any of the 924 sets.
- `AME125/FormalTarget.lean` puts it together as `AME125.ame_12_5_open : ExistsAME 12 5`.
- `AME125/Control.lean` removes six edges from the graph, the ones between party 0 and parties 6 to 11, and proves the result is not AME. It uses the same reduction formula and none of the certificates, so the formula isn't passing for a trivial reason.

Computed:

- `AME125/Data.lean` holds the authors' table and, for each of the 924 sets of six parties, the inverse of its block. Both are generated from `data/` by `scripts/gen_lean_data.py`.
- The Lean kernel multiplies out every inverse, mod 5, and checks the list covers all 924 sets. This takes about two minutes.

The statement is the same term as Formal Conjectures' `OpenQuantumProblem35.ame_12_5_open`. The proof uses only `propext`, `Classical.choice` and `Quot.sound`. The kernel checks of the certificates use at most `propext`.

## Building

It needs Lean v4.33.1 and depends on Formal Conjectures at commit `9833012f`.

```
lake exe cache get
lake build
```

A fresh build first compiles Formal Conjectures' support library. The kernel checks in `AME125/Certificate.lean` take about two minutes. On a machine with limited memory set `LEAN_NUM_THREADS` to a small number first.

To rerun the checks, one at a time:

```
lake env lean audit/Audit.lean
lake env lean audit/Vacuity.lean
python audit/lexical.py
lake exe runLinter AME125
lake exe lint-style AME125
python scripts/check_blocks.py data/theta_ame125.txt
python scripts/check_certs.py data/theta_ame125.txt data/certs.txt
python scripts/check_criterion.py
```

`audit/lexical.py` also regenerates the certificates and the Lean data from the authors' table and checks both match exactly. `scripts/check_blocks.py` checks all 924 blocks independently of Lean. `scripts/check_criterion.py` needs numpy and checks the graph-state criterion numerically on smaller cases. Each script exits with an error if its check fails.

## How it was made

I used Claude Code to draft the Lean. I've checked every line myself and can explain all of it. The authors' table was checked independently, exactly mod 5, before any Lean was written.

## About

I'm Zayn Blore. My main project is [csd-lean4](https://github.com/zblore/csd-lean4), the Lean library behind my work on Constraint-Surface Dynamics.
