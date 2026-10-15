# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_constancy-a1.boundary_ray_test-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b3d1ddea13/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_constancy-a1`
- Child key: `boundary_ray_test`
- Declaration: `Submission.idtp_fons_odc_rc_boundary_ray_test`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 1), C.boundary = 0 → ∀ (F : Finset (Euclid P)) (G : Euclid P → ℝ → ℝ), (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, C ω = ∑ e ∈ F, ∫ t in Ioi (0 : ℝ), G e t * (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) → ∀ f : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → ∑ e ∈ F, ∫ t in Ioi (0 : ℝ), G e t * deriv (fun s : ℝ => f (s • e)) t = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
