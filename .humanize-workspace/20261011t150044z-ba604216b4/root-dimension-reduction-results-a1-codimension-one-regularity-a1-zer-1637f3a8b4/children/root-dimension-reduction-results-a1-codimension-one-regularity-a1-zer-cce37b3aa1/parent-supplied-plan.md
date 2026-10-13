# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.graph_integral_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-cce37b3aa1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Child key: `graph_integral_limit`
- Declaration: `Submission.codim1_zsl_fl_graph_integral_tendsto`
- Exact Lean type: `∀ (m k P : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (b : Euclid k) (R : ℝ) (β : Euclid P → Covector (Euclid P) m) (gs : ℕ → Euclid m → Euclid k) (As : ℕ → Set (Euclid m)) (A : Set (Euclid m)), Continuous β → HasCompactSupport β → (∀ i, MeasurableSet (As i)) → MeasurableSet A → Tendsto (fun i => volume (symmDiff (As i) A ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) → (∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, DifferentiableAt ℝ (gs i) w) → (∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, ‖gs i w - b‖ < ε ∧ ‖fderiv ℝ (gs i) w‖ < ε) → Tendsto (fun i => ∫ w in As i ∩ ball 0 R, β (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w (EuclideanSpace.single j (1 : ℝ)))) atTop (𝓝 (∫ w in A ∩ ball 0 R, β (ι w + ι' b) (fun j => ι (EuclideanSpace.single j (1 : ℝ)))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
