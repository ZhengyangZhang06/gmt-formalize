# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.antipodal-a1.ray_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-846351711b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.antipodal-a1`
- Child key: `ray_mass`
- Declaration: `Submission.idtp_fons_odc_antipodal_ray_mass`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 1) (R : IMRep (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → ∀ m : Euclid P → ℤ, R.Represents C → (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ e ∈ F, ENNReal.ofReal |(m e : ℝ)| * volume (Ioi (0 : ℝ) ∩ (fun t : ℝ => t • e) ⁻¹' A)) → ∀ r : ℝ, C.massOn (ball (0 : Euclid P) r) = ENNReal.ofReal ((∑ e ∈ F, |(m e : ℝ)|) * r)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.im_mass_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
