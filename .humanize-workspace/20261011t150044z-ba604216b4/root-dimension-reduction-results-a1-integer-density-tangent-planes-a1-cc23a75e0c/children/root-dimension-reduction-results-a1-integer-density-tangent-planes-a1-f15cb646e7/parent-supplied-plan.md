# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_current_rep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-f15cb646e7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1`
- Child key: `ray_current_rep`
- Declaration: `Submission.idtp_fons_odc_ray_current_rep`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → ∀ m : Euclid P → ℤ, (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, C ω = ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (0 : ℝ), (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) → ∃ R : IMRep (univ : Set (Euclid P)) 1, R.Represents C ∧ ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ e ∈ F, ENNReal.ofReal |(m e : ℝ)| * volume (Ioi (0 : ℝ) ∩ (fun t : ℝ => t • e) ⁻¹' A)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
