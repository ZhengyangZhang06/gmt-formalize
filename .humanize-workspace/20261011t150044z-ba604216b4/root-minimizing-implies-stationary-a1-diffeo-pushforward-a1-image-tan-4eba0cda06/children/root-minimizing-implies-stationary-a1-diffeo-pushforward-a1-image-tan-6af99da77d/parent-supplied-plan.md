# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1.composed_piece-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-6af99da77d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1`
- Child key: `composed_piece`
- Declaration: `Submission.dpf_itt_comp_bilipschitz_piece`
- Exact Lean type: `∀ (P n : ℕ) (F : Euclid n → Euclid P) (φ : Euclid P → Euclid P) (B : Set (Euclid n)) (L Λ Λ' : NNReal) (m : ℝ), LipschitzWith L F → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → Differentiable ℝ φ → (∀ x, Injective (fderiv ℝ φ x)) → LipschitzWith Λ φ → AntilipschitzWith Λ' φ → LipschitzWith (Λ * L) (φ ∘ F) ∧ (∃ m' : ℝ, 0 < m' ∧ ∀ a ∈ B, ∀ a' ∈ B, m' * ‖a - a'‖ ≤ ‖(φ ∘ F) a - (φ ∘ F) a'‖) ∧ (∀ a ∈ B, DifferentiableAt ℝ (φ ∘ F) a ∧ Injective (fderiv ℝ (φ ∘ F) a)) ∧ ∀ a ∈ B, LinearMap.range (fderiv ℝ (φ ∘ F) a : Euclid n →ₗ[ℝ] Euclid P) = Submodule.map (fderiv ℝ φ (F a) : Euclid P →ₗ[ℝ] Euclid P) (LinearMap.range (fderiv ℝ F a : Euclid n →ₗ[ℝ] Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
