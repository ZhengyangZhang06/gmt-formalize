# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1.discrete_growth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-c16f795a32/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1`
- Child key: `discrete_growth`
- Declaration: `Submission.codim1_rdo_dg_vdl_discrete_growth`
- Exact Lean type: `∀ (m : ℕ) (K ρ₁ : ℝ) (V : ℝ → ℝ), 0 < K → (∀ r : ℝ, 0 < r → r < ρ₁ → 0 < V r) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → V ρ ^ ((m : ℝ) / (m + 1)) ≤ K / δ * (V (ρ + δ) - V ρ)) → ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → (ρ / (2 * K * (m + 1))) ^ (m + 1) ≤ V ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
