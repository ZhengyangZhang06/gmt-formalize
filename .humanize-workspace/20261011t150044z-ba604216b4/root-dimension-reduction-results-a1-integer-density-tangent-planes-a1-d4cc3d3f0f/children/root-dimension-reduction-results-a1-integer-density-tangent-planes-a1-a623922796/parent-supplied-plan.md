# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.vague_closed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a623922796/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child key: `vague_closed`
- Declaration: `Submission.idtp_fons_cc_psf_vague_closed`
- Exact Lean type: `∀ (P n : ℕ) (μ₀ : Measure (Euclid P)), μ₀ univ ≠ ∞ → ∀ (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (ν : Measure (Euclid P)) (K : Set (Euclid P)), (∀ i, 0 < lams i ∧ lams i ≤ 1 ∧ ‖xs i‖ ≤ 1 - lams i) → (∀ K' : Set (Euclid P), IsCompact K' → ν K' ≠ ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun i => ∫ x, f x ∂(ENNReal.ofReal ((lams i)⁻¹ ^ n) • μ₀.map (dilation (xs i) (lams i)))) atTop (𝓝 (∫ x, f x ∂ν))) → IsCompact K → (∀ i, ¬ K ⊆ dilation (xs i) (lams i) '' ball 0 2) → ∃ (x : Euclid P) (lam : ℝ), (0 < lam ∧ lam ≤ 1 ∧ ‖x‖ ≤ 1 - lam) ∧ ν = (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) ∧ ¬ K ⊆ dilation x lam '' ball 0 2`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.domain_geometry-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.vague_unique-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.param_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
