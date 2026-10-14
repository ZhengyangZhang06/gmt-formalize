# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.sing_mem_of_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-sing-mem-of-tendsto-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1`
- Child key: `sing_mem_of_tendsto`
- Declaration: `Submission.adr_sing_mem_of_tendsto`
- Exact Lean type: `∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ ψ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) → ∀ (zs : ℕ → Euclid P) (z : Euclid P), (∀ k, zs k ∈ ball (0 : Euclid P) 1 ∩ sing (φs k)) → Tendsto zs atTop (𝓝 z) → z ∈ sing ψ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
