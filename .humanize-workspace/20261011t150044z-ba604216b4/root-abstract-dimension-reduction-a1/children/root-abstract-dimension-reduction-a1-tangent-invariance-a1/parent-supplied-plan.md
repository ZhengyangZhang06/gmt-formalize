# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.tangent_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-tangent-invariance-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1`
- Child key: `tangent_invariance`
- Declaration: `Submission.adr_tangent_invariance`
- Exact Lean type: `∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → ∀ φ ∈ F, ∀ S : Submodule ℝ (Euclid P), (∀ y ∈ S, ∀ lam : ℝ, 0 < lam → ∀ x, φ (y + lam • x) = φ x) → ∀ (x : Euclid P) (lams : ℕ → ℝ) (ψ : Euclid P → Euclid Q), (∀ k, 0 < lams k) → Tendsto lams atTop (𝓝 0) → (∀ k, (fun z => φ (x + lams k • z)) ∈ F) → ψ ∈ F → (∀ lam : ℝ, 0 < lam → ∀ z, ψ (lam • z) = ψ z) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z, f z • φ (x + lams k • z) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ z, f z • ψ z ∂μH[(n : ℝ)]))) → ∀ y ∈ S ⊔ Submodule.span ℝ {x}, ∀ lam : ℝ, 0 < lam → ∀ z, ψ (y + lam • z) = ψ z`

## Sibling prerequisites

- `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
