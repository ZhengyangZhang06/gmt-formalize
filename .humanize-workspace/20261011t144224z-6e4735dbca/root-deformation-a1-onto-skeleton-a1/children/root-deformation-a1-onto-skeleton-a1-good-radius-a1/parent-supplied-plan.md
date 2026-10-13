# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.good_radius-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-good-radius-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1`
- Child key: `good_radius`
- Declaration: `Submission.deformation_good_radius`
- Exact Lean type: `∀ (a b : ℝ) (g : ℝ → ℝ≥0∞) (K : ℝ≥0∞) (N : Set ℝ), a < b → Measurable g → ∫⁻ t in Ioo a b, g t ≤ K → volume N = 0 → ∃ t ∈ Ioo a b, t ∉ N ∧ g t ≤ 2 * K / ENNReal.ofReal (b - a)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
