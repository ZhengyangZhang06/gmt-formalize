# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1.gram_cone-a1.orth_residual-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-parametr-95c796c85b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1.gram_cone-a1`
- Child key: `orth_residual`
- Declaration: `Submission.ecf_cp_gc_orth_residual`
- Exact Lean type: `∀ (P k : ℕ) (a : Euclid P) (w : Fin k → Euclid P), ∃ c : Fin k → ℝ, (∀ j : Fin k, inner ℝ (a - ∑ l, c l • w l) (w j) = 0) ∧ ‖a - ∑ l, c l • w l‖ ≤ ‖a‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
