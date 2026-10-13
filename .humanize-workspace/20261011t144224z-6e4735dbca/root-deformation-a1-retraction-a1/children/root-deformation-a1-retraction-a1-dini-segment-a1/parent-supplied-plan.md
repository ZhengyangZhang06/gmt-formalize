# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.retraction-a1.dini_segment-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1-dini-segment-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.retraction-a1`
- Child key: `dini_segment`
- Declaration: `Submission.deformation_retraction_dini_segment`
- Exact Lean type: `∀ (N : ℕ) (γ : ℝ → Eucl N) (K : ℝ), (∀ s ∈ Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s' ∈ Icc (0 : ℝ) 1, |s' - s| < δ → ‖γ s' - γ s‖ ≤ (K + ε) * |s' - s|) → ‖γ 1 - γ 0‖ ≤ K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
