# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1.radii-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-tangent-keeps-measure-a1-radii-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1`
- Child key: `radii`
- Declaration: `Submission.adr_exists_strictAnti_radii`
- Exact Lean type: `∀ (Q : ℝ → Prop) (δ₀ : ℝ), 0 < δ₀ → (∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ Q ρ) → ∃ ρs : ℕ → ℝ, (∀ k, 0 < ρs k) ∧ (∀ k, ρs k < δ₀) ∧ StrictAnti ρs ∧ Tendsto ρs atTop (𝓝 0) ∧ ∀ k, Q (ρs k)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
