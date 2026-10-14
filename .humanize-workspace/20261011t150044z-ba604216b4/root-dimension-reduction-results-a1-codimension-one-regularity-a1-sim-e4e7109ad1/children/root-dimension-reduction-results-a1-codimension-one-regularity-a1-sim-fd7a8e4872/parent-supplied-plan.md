# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.quasilinear_smooth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-fd7a8e4872/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `quasilinear_smooth`
- Declaration: `Submission.codim1_hcp_sr_quasilinear_smooth`
- Exact Lean type: `∀ (m k : ℕ) (G : (Euclid m →L[ℝ] Euclid k) → (Euclid m →L[ℝ] Euclid k)), 1 ≤ m → ContDiff ℝ (⊤ : ℕ∞) G → G 0 = 0 → fderiv ℝ G 0 = 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (Ω : Set (Euclid m)) (u : Euclid m → Euclid k), IsOpen Ω → ContDiffOn ℝ 1 u Ω → (∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ ε₀) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω → ∫ x in Ω, ∑ j : Fin m, inner ℝ (fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in Ω, ∑ j : Fin m, inner ℝ (G (fderiv ℝ u x) (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → ∀ r : ℕ, ContDiffOn ℝ r u Ω`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.c1alpha_estimate-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.difference_quotient-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.holder_algebra-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.linear_bootstrap-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
