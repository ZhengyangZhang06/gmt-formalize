# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-tangent-keeps-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1`
- Child key: `tangent_keeps_measure`
- Declaration: `Submission.adr_tangent_keeps_measure`
- Exact Lean type: `∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ ℓ : ℝ, 0 < ℓ → ∀ φ ∈ F, μH[ℓ] {x | x ∈ sing φ ∩ ball (0 : Euclid P) 1 ∧ ¬ ∃ (lams : ℕ → ℝ) (ψ : Euclid P → Euclid Q), (∀ k, 0 < lams k) ∧ (∀ k, lams k < 1) ∧ (∀ k, ‖x‖ ≤ 1 - lams k) ∧ Tendsto lams atTop (𝓝 0) ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z, f z • φ (x + lams k • z) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ z, f z • ψ z ∂μH[(n : ℝ)]))) ∧ (∀ lam : ℝ, 0 < lam → ∀ z, ψ (lam • z) = ψ z) ∧ 0 < μH[ℓ] (sing ψ ∩ ball (0 : Euclid P) 1)} = 0`

## Sibling prerequisites

- `root.abstract_dimension_reduction-a1.content_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
