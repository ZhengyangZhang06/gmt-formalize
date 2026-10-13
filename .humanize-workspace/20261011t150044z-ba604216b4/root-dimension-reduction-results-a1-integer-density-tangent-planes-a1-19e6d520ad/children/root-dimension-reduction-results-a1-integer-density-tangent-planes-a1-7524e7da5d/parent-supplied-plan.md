# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.blowup_translation_invariance-a1.blowup_translate_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7524e7da5d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.blowup_translation_invariance-a1`
- Child key: `blowup_translate_integral`
- Declaration: `Submission.idtp_cttp_bti_blowup_translate_integral`
- Exact Lean type: `∀ (P n : ℕ) (μ ν : Measure (Euclid P)) (p : Euclid P) (lam t : ℝ), 0 < lam → 0 < 1 + lam * t → (∀ c : ℝ, 0 < c → ∀ A : Set (Euclid P), MeasurableSet A → μ ((fun x => c • x) '' A) = ENNReal.ofReal (c ^ n) * μ A) → (∀ B : Set (Euclid P), MeasurableSet B → ν B = ENNReal.ofReal (lam⁻¹ ^ n) * μ (dilation p lam ⁻¹' B)) → ∀ f : Euclid P → ℝ, Continuous f → ∫ y, f (y - t • p) ∂ν = (1 + lam * t) ^ n * ∫ y, f ((1 + lam * t) • y) ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
