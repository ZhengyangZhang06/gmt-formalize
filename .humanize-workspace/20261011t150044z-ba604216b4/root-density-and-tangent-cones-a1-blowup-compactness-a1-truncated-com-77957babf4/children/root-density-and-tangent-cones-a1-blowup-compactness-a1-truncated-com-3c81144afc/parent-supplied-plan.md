# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.radial_slice-a1.radius_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-3c81144afc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.radial_slice-a1`
- Child key: `radius_bound`
- Declaration: `Submission.dtc_bc_tc_rs_radius_bound`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U (m + 1)) (Rp : IMRep U (m + 1)) (R t : ℝ), closedBall (0 : Euclid P) R ⊆ U → Rp.Represents S → (∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball 0 R → S.boundary ω = 0) → t < R → ∀ (β : TestFormOn (univ : Set (Euclid P)) m) (s : ℝ), (∀ x, covectorEuclideanNorm ((β : DifferentialForm (Euclid P) m) x) ≤ s) → ENNReal.ofReal |∫ x in Rp.carrier ∩ ball 0 t, (Rp.mult x : ℝ) * Rp.orient x (exteriorDerivative (β : DifferentialForm (Euclid P) m) x) ∂μHE[m + 1]| ≤ ENNReal.ofReal s * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * Rp.measure {x : Euclid P | t - h < ‖x‖ ∧ ‖x‖ < t}) (𝓝[>] 0)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.radial_slice-a1.cutoff_defect-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.level_cutoff-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1.cutoff_integral_tendsto-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1.liminf_bound-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1.pairing_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
