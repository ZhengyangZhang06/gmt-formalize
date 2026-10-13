# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.normal_halfspace-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-f83d13f613/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child key: `normal_halfspace`
- Declaration: `Submission.codim1_rdo_dg_tma_normal_halfspace`
- Exact Lean type: `∀ (m : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1)) (v : Euclid (m + 1)) (h : Euclid (m + 1) → ℝ), ‖v‖ = 1 → (∀ x, inner ℝ (ι x) v = 0) → ContDiff ℝ 1 h → HasCompactSupport h → ∫ w in {w : Euclid (m + 1) | 0 < inner ℝ w v}, fderiv ℝ h w v = -∫ x, h (ι x)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.orthogonal_fubini-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
