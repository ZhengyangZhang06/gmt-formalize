# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.holder_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-2475a728e0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `holder_algebra`
- Declaration: `Submission.codim1_hcp_sr_holder_algebra`
- Exact Lean type: `∀ (m : ℕ) (α : ℝ) (Ω : Set (Euclid m)), IsOpen Ω → 0 < α → α ≤ 1 → ∀ l : ℕ, (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E), (ContDiffOn ℝ l (fun _ : Euclid m => c) Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l (fun _ : Euclid m => c) y - iteratedFDeriv ℝ l (fun _ : Euclid m => c) z‖ ≤ C * ‖y - z‖ ^ α)) ∧ (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : Euclid m → E), (ContDiffOn ℝ l f Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l f y - iteratedFDeriv ℝ l f z‖ ≤ C * ‖y - z‖ ^ α) → (ContDiffOn ℝ l g Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l g y - iteratedFDeriv ℝ l g z‖ ≤ C * ‖y - z‖ ^ α) → (ContDiffOn ℝ l (fun x => f x + g x) Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l (fun x => f x + g x) y - iteratedFDeriv ℝ l (fun x => f x + g x) z‖ ≤ C * ‖y - z‖ ^ α)) ∧ (∀ (E₁ E₂ E₃ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] (β : E₁ →L[ℝ] E₂ →L[ℝ] E₃) (f₁ : Euclid m → E₁) (f₂ : Euclid m → E₂), (ContDiffOn ℝ l f₁ Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l f₁ y - iteratedFDeriv ℝ l f₁ z‖ ≤ C * ‖y - z‖ ^ α) → (ContDiffOn ℝ l f₂ Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l f₂ y - iteratedFDeriv ℝ l f₂ z‖ ≤ C * ‖y - z‖ ^ α) → (ContDiffOn ℝ l (fun x => β (f₁ x) (f₂ x)) Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l (fun x => β (f₁ x) (f₂ x)) y - iteratedFDeriv ℝ l (fun x => β (f₁ x) (f₂ x)) z‖ ≤ C * ‖y - z‖ ^ α)) ∧ (∀ (E₁ E₂ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (Φ : E₁ → E₂) (f : Euclid m → E₁), ContDiff ℝ (⊤ : ℕ∞) Φ → (ContDiffOn ℝ l f Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l f y - iteratedFDeriv ℝ l f z‖ ≤ C * ‖y - z‖ ^ α) → (ContDiffOn ℝ l (fun x => Φ (f x)) Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l (fun x => Φ (f x)) y - iteratedFDeriv ℝ l (fun x => Φ (f x)) z‖ ≤ C * ‖y - z‖ ^ α)) ∧ (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euclid m → E), ContDiffOn ℝ (l + 1) f Ω → (ContDiffOn ℝ l f Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l f y - iteratedFDeriv ℝ l f z‖ ≤ C * ‖y - z‖ ^ α)) ∧ (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euclid m → E), ContDiffOn ℝ 1 f Ω → ((ContDiffOn ℝ (l + 1) f Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ (l + 1) f y - iteratedFDeriv ℝ (l + 1) f z‖ ≤ C * ‖y - z‖ ^ α) ↔ (ContDiffOn ℝ l (fun x => fderiv ℝ f x) Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l (fun x => fderiv ℝ f x) y - iteratedFDeriv ℝ l (fun x => fderiv ℝ f x) z‖ ≤ C * ‖y - z‖ ^ α)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
