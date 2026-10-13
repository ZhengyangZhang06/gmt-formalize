# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.good_center-a1.tube_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-good-center-a1-tube-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.good_center-a1`
- Child key: `tube_cover`
- Declaration: `Submission.dgc_tube_cover`
- Exact Lean type: `∀ (d k : ℕ), k ≤ d → ∀ (a : Eucl d) (La : Set (Eucl d)), La = {y | ∃ J : Finset (Fin d), J.card = k ∧ ∀ i ∈ J, ∃ n : ℤ, y i - a i = n} → ∀ (σ : ℝ) (x : Eucl d), infDist x La < σ → ∃ J : Finset (Fin d), J.card = k ∧ ∃ z : J → ℤ, ∑ i : J, (x i - a i - z i) ^ 2 < σ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
