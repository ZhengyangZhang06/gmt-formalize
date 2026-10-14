# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1.sobolev_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-07805786db/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1`
- Child key: `sobolev_limit`
- Declaration: `Submission.codim1_rdo_dg_sp_sobolev_limit`
- Exact Lean type: `∀ (P : ℕ) (p c : ℝ), 0 < p → 0 ≤ c → (∀ w : Euclid P → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → (∫ z, |w z| ^ p) ^ p⁻¹ ≤ c * ∫ z, ‖fderiv ℝ w z‖) → ∀ (u : Euclid P → ℝ) (M : ℝ), Integrable u → HasCompactSupport u → (∀ g : Euclid P → Euclid P, ContDiff ℝ 1 g → HasCompactSupport g → (∀ z, ‖g z‖ ≤ 1) → |∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| ≤ M) → ∀ η : ℕ → Euclid P → ℝ, (∀ k, ContDiff ℝ 1 (η k)) → (∀ k, HasCompactSupport (η k)) → (∀ k z, 0 ≤ η k z) → (∀ k z, η k (-z) = η k z) → (∀ k, ∫ z, η k z = 1) → (∀ᵐ x, Tendsto (fun k => convolution (η k) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop (𝓝 (u x))) → (∫ z, |u z| ^ p) ^ p⁻¹ ≤ c * M`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1.mollify_variation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
