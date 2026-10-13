# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.atoms-a1.carried-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-ab30bdbafc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.atoms-a1`
- Child key: `carried`
- Declaration: `Submission.cbr_ci_cp_atm_transversal_carried`
- Exact Lean type: `∀ (P n : ℕ) (ν σ : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (Z : Set (Euclid P)), Module.finrank ℝ V = n → σ (Vᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in (V : Set (Euclid P)), σ ((fun y => t + y) ⁻¹' A) ∂μHE[n]) → MeasurableSet Z → (∀ᵐ x ∂ν, x - V.starProjection x ∈ Z) → σ Zᶜ = 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.subspace_ball_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
