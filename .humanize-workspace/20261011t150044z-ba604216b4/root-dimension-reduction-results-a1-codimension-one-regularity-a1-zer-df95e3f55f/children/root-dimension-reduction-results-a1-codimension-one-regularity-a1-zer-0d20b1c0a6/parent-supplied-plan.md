# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.integral_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0d20b1c0a6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1`
- Child key: `integral_transfer`
- Declaration: `Submission.codim1_zsl_ga_integral_transfer`
- Exact Lean type: `∀ (m P : ℕ) (μ : Measure (Euclid P)) (G : Euclid m → Euclid P) (J : Euclid m → ℝ) (A : Set (Euclid m)) (f : Euclid P → ℝ), MeasurableSet A → ContinuousOn G A → InjOn G A → Measurable J → (∀ w ∈ A, 0 ≤ J w) → (∀ B : Set (Euclid m), MeasurableSet B → B ⊆ A → μ (G '' B) = ∫⁻ w in B, ENNReal.ofReal (J w)) → ∫ y in G '' A, f y ∂μ = ∫ w in A, J w * f (G w)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
