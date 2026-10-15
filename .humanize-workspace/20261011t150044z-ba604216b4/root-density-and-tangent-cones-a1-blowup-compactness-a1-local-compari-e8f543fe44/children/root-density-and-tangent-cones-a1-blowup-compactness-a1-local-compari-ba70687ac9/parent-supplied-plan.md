# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1.boundary_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-ba70687ac9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1`
- Child key: `boundary_mass`
- Declaration: `Submission.dtc_bc_lc_fd_lz_boundary_mass`
- Exact Lean type: `∀ (P m : ℕ) (U V : Set (Euclid P)) (T T' : GeometricCurrentOn U (m + 1)) (R R' : IMRep U (m + 1)) (t₀ : ℝ), closedBall (0 : Euclid P) t₀ ⊆ V → R.Represents T → R'.Represents T' → R'.carrier = R.carrier ∩ ball (0 : Euclid P) t₀ → R'.mult = R.mult → R'.orient = R.orient → T'.boundary.mass ≤ 2 * T.boundary.massOn V + 2 * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * R.measure {x : Euclid P | t₀ - h < ‖x‖ ∧ ‖x‖ < t₀}) (𝓝[>] 0)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1.cutoff_estimate-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.level_cutoff-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1.cutoff_integral_tendsto-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
