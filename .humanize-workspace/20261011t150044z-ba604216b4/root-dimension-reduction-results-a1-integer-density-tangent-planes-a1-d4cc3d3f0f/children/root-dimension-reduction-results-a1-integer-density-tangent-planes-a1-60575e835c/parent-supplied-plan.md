# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.param_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-60575e835c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child key: `param_continuity`
- Declaration: `Submission.idtp_fons_cc_psf_param_continuity`
- Exact Lean type: `∀ (P n : ℕ) (μ₀ : Measure (Euclid P)) (f : Euclid P → ℝ) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (x : Euclid P) (lam : ℝ), μ₀ univ ≠ ∞ → Continuous f → HasCompactSupport f → (∀ i, 0 < lams i) → 0 < lam → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 lam) → Tendsto (fun i => ∫ v, f v ∂(ENNReal.ofReal ((lams i)⁻¹ ^ n) • μ₀.map (dilation (xs i) (lams i)))) atTop (𝓝 (∫ v, f v ∂(ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
