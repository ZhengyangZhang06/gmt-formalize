# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1.gram_cone-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-parametr-e2b63fa3a9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1`
- Child key: `gram_cone`
- Declaration: `Submission.ecf_cp_gram_cone`
- Exact Lean type: `∀ (P k : ℕ) (a : Euclid P) (w : Fin k → Euclid P), (∀ t : ℝ, 0 ≤ t → Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons a (t • w) : Fin (k + 1) → Euclid P) i) ((Fin.cons a (t • w) : Fin (k + 1) → Euclid P) j))) = t ^ k * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons a w : Fin (k + 1) → Euclid P) i) ((Fin.cons a w : Fin (k + 1) → Euclid P) j)))) ∧ Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons a w : Fin (k + 1) → Euclid P) i) ((Fin.cons a w : Fin (k + 1) → Euclid P) j))) ≤ ‖a‖ * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin k => inner ℝ (w i) (w j)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
