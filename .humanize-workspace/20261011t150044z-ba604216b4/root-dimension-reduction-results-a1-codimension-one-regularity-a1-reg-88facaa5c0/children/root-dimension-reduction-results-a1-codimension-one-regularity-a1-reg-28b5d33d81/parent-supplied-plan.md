# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1.gns_real_of_lintegral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-28b5d33d81/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1`
- Child key: `gns_real_of_lintegral`
- Declaration: `Submission.codim1_rdo_dg_sp_gns_real_of_lintegral`
- Exact Lean type: `∀ (P : ℕ) (p : ℝ) (C : NNReal), 0 < p → (∀ w : Euclid P → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → ∫⁻ x, ‖w x‖ₑ ^ p ≤ (C : ℝ≥0∞) * (∫⁻ x, ‖fderiv ℝ w x‖ₑ) ^ p) → ∃ c : ℝ, 0 < c ∧ ∀ w : Euclid P → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → (∫ z, |w z| ^ p) ^ p⁻¹ ≤ c * ∫ z, ‖fderiv ℝ w z‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
