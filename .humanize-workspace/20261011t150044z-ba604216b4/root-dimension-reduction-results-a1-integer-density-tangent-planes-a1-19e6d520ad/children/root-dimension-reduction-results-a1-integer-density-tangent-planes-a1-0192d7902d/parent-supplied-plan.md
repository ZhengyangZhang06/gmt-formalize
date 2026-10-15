# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.blowup_translation_invariance-a1.rescaled_tests_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-0192d7902d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.blowup_translation_invariance-a1`
- Child key: `rescaled_tests_tendsto`
- Declaration: `Submission.idtp_cttp_bti_rescaled_tests_tendsto`
- Exact Lean type: `∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)) (s : ℕ → ℝ) (f : Euclid P → ℝ), (∀ j, ∀ K : Set (Euclid P), IsCompact K → μs j K < ∞) → (∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => ∫ x, g x ∂(μs j)) atTop (𝓝 (∫ x, g x ∂μ))) → Tendsto s atTop (𝓝 1) → Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ y, f (s j • y) ∂(μs j)) atTop (𝓝 (∫ x, f x ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
