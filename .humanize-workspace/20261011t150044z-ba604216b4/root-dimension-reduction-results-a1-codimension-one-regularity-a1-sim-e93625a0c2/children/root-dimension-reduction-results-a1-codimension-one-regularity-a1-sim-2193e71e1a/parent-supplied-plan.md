# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.jacobian_stationary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-2193e71e1a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1`
- Child key: `jacobian_stationary`
- Declaration: `Submission.codim1_hcp_fv_jacobian_minimal_stationary`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Euclid P)) (Z : Euclid P → Euclid P), IsEmbeddedSubmanifold 1 m M → ContDiff ℝ 1 Z → HasCompactSupport Z → μHE[m] (M ∩ tsupport Z) ≠ ∞ → (∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ → μHE[m] (M ∩ tsupport Z) ≤ ∫⁻ x in M ∩ tsupport Z, ENNReal.ofReal (Real.sqrt ((((fderiv ℝ (fun y => y + t • Z y) x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL).adjoint ∘L ((fderiv ℝ (fun y => y + t • Z y) x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL)).det)) ∂μHE[m]) → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ Z x).toLinearMap) ∂μHE[m] = 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.regular_point_density-a1.locally_closed-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.tangent_projection-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.trace_bound-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.jacobian_first_order-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
