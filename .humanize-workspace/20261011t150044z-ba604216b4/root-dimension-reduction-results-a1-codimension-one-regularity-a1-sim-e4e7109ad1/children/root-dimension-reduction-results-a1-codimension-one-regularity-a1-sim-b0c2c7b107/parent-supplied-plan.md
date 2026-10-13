# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.c1alpha_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b0c2c7b107/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `c1alpha_estimate`
- Declaration: `Submission.codim1_hcp_sr_c1alpha_estimate`
- Exact Lean type: `∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → α < 1 → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ K R : ℝ, 0 ≤ K → 0 < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Euclid m) (w : Euclid m → Euclid k) (F : Euclid m → (Euclid m →L[ℝ] Euclid k)), ContDiffOn ℝ 1 w (ball x₀ R) → ContinuousOn F (ball x₀ R) → (∀ x ∈ ball x₀ R, ‖w x‖ ≤ K) → (∀ x ∈ ball x₀ R, ‖F x‖ ≤ ε₁ * ‖fderiv ℝ w x‖ + K) → (∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → closedBall x ρ ⊆ ball x₀ R → ∃ c : Euclid m →L[ℝ] Euclid k, ∫ z in ball x ρ, ‖F z - c‖ ^ 2 ≤ ε₁ * ∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2 + K * ρ ^ (2 * α) * ∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2 + K * ρ ^ ((m : ℝ) + 2 * α)) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball x₀ R → ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (F x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → (∀ x ∈ ball x₀ (R / 4), ‖fderiv ℝ w x‖ ≤ C) ∧ ∀ x ∈ ball x₀ (R / 4), ∀ y ∈ ball x₀ (R / 4), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.harmonic_replacement-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.harmonic_decay-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.campanato_lemmas-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
