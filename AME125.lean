import AME125.FormalTarget
import AME125.Control

/-!
# AME(12,5) in Lean

A Lean 4 proof that an AME(12,5) state exists, against Formal Conjectures' Open Quantum
Problem 35: `AME125.ame_12_5_open : OpenQuantumProblem35.ExistsAME 12 5`. The witness is the
graph state of S. Bevins and Y. Bidav's graph over `ZMod 5`; the proof is a general graph-state
criterion (`AME125.GraphState`) and 924 kernel-checked cut certificates (`AME125.Certificate`).
`AME125.Control` proves a broken graph is not AME.
-/
