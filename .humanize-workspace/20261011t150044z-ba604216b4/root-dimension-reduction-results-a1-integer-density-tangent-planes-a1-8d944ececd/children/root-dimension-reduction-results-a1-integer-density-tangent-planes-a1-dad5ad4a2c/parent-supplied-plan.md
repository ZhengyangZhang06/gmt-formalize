# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.finite_rays-a1.cone_scaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-dad5ad4a2c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.finite_rays-a1`
- Child key: `cone_scaling`
- Declaration: `Submission.idtp_fons_odc_fr_cone_scaling`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W → μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W) → ∀ K : Set (Euclid P), IsOpen K → (∀ c : ℝ, 0 < c → ∀ x ∈ K, c • x ∈ K) → ∀ r : ℝ, 0 < r → μ (K ∩ ball 0 r) = ENNReal.ofReal r * μ (K ∩ ball 0 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
