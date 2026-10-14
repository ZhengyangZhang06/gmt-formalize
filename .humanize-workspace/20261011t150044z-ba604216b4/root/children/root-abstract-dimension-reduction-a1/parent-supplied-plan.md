# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `abstract_dimension_reduction`
- Declaration: `Submission.abstract_dimension_reduction`
- Exact Lean type: `∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (L : Submodule ℝ (Euclid P)) (c : Euclid Q), Module.finrank ℝ L = n → φ = Set.indicator (L : Set (Euclid P)) (fun _ => c) → sing φ = ∅) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → (∀ φ ∈ F, ball (0 : Euclid P) 1 ∩ sing φ = ∅) ∨ ∃ d : ℕ, d + 1 ≤ n ∧ (∀ φ ∈ F, ∀ α : ℝ, 0 < α → μH[(d : ℝ) + α] (sing φ ∩ ball (0 : Euclid P) 1) = 0) ∧ (∃ ψ ∈ F, ∃ L : Submodule ℝ (Euclid P), Module.finrank ℝ L = d ∧ sing ψ = (L : Set (Euclid P)) ∧ ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) ∧ (d = 0 → ∀ φ ∈ F, ∀ σ : ℝ, σ < 1 → (sing φ ∩ ball (0 : Euclid P) σ).Finite)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
