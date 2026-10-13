# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.cutoff_estimates-a1.radial_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-04d1586b61/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.cutoff_estimates-a1`
- Child key: `radial_cutoff`
- Declaration: `Submission.codim1_rdo_dg_ce_radial_cutoff`
- Exact Lean type: `∀ (P : ℕ) (y : Euclid P) (ρ δ : ℝ), 0 < ρ → 0 < δ → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧ (∀ z ∈ closedBall y ρ, ζ z = 1) ∧ tsupport ζ ⊆ closedBall y (ρ + δ) ∧ (∀ z, ‖fderiv ℝ ζ z‖ ≤ 3 / (2 * δ)) ∧ (∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0) ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ r : ℝ, ρ ≤ r ∧ r < ρ + δ ∧ {z | t ≤ ζ z} = closedBall y r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
