# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.linear_bootstrap-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-281bba6d0a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `linear_bootstrap`
- Declaration: `Submission.codim1_hcp_sr_linear_bootstrap`
- Exact Lean type: `∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → α < 1 → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (Ω : Set (Euclid m)) (l : ℕ) (w : Euclid m → Euclid k) (B : Euclid m → ((Euclid m →L[ℝ] Euclid k) →L[ℝ] (Euclid m →L[ℝ] Euclid k))) (g : Euclid m → (Euclid m →L[ℝ] Euclid k)), IsOpen Ω → ContDiffOn ℝ 1 w Ω → (∀ x ∈ Ω, ‖B x‖ ≤ ε₁) → (ContDiffOn ℝ l B Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l B y - iteratedFDeriv ℝ l B z‖ ≤ C * ‖y - z‖ ^ α) → (ContDiffOn ℝ l g Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l g y - iteratedFDeriv ℝ l g z‖ ≤ C * ‖y - z‖ ^ α) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω → ∫ x in Ω, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in Ω, ∑ j : Fin m, inner ℝ ((B x (fderiv ℝ w x) + g x) (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → (ContDiffOn ℝ (l + 1) w Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ (l + 1) w y - iteratedFDeriv ℝ (l + 1) w z‖ ≤ C * ‖y - z‖ ^ α)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.c1alpha_estimate-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.difference_quotient-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.holder_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
