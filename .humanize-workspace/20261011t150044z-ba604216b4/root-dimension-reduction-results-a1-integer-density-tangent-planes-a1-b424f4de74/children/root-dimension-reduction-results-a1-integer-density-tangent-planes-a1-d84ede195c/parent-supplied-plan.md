# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.tilt_decay-a1.blowup_eval-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d84ede195c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1.tilt_decay-a1`
- Child key: `blowup_eval`
- Declaration: `Submission.idtp_cse_bml_td_blowUp_smul_form_eval`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (a : Euclid P) (t : ℝ) (ht : 0 < t) (g : Euclid P → ℝ) (β : Covector (Euclid P) n) (ω : TestFormOn (univ : Set (Euclid P)) n), R.Represents C → (∀ x, (ω : DifferentialForm (Euclid P) n) x = g x • β) → currentEval (blowUp C a t ht.ne') (ω : DifferentialForm (Euclid P) n) = t⁻¹ ^ n * ∫ y, g (dilation a t y) * R.orient y β ∂R.measure`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_scaling-a1.testform_correspondence-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.imrep_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
