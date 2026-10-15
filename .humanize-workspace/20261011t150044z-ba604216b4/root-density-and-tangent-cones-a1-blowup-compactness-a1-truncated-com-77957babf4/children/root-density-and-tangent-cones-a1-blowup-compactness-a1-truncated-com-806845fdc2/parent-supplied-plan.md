# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.radial_slice-a1.cutoff_defect-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-806845fdc2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.radial_slice-a1`
- Child key: `cutoff_defect`
- Declaration: `Submission.dtc_bc_tc_rs_cutoff_defect`
- Exact Lean type: `∀ (P m : ℕ) (U V : Set (Euclid P)) (S : GeometricCurrentOn U (m + 1)) (Rp : IMRep U (m + 1)) (g : Euclid P → ℝ) (β : TestFormOn (univ : Set (Euclid P)) m), Rp.Represents S → (∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ V → S.boundary ω = 0) → ContDiff ℝ (⊤ : ℕ∞) g → tsupport g ⊆ U → tsupport g ⊆ V → ENNReal.ofReal |∫ x in Rp.carrier, g x * ((Rp.mult x : ℝ) * Rp.orient x (exteriorDerivative (β : DifferentialForm (Euclid P) m) x)) ∂μHE[m + 1]| ≤ ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm ((β : DifferentialForm (Euclid P) m) x)) ∂Rp.measure`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.leibniz-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.pairing_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
