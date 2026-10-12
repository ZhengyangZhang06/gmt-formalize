# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.whitney_extension-a1.whitney_gluing-a1.local_structure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-gluing-a1-local-structure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.whitney_extension-a1.whitney_gluing-a1`
- Child key: `local_structure`
- Declaration: `Submission.whitney_gluing_local_structure`
- Exact Lean type: `∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (g : Rn n → ℝ), IsClosed A → (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) → (∀ i, ∀ x ∉ A, 0 ≤ φ i x) → (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) → (∀ x ∉ A, ∑ᶠ i, φ i x = 1) → (∀ x ∉ A, g x = ∑ᶠ i, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ∀ x ∉ A, ContDiffAt ℝ 1 g x ∧ ∃ S : Finset ι, (∀ i ∈ S, 0 < φ i x) ∧ ∑ i ∈ S, φ i x = 1 ∧ g x = ∑ i ∈ S, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i)) ∧ fderiv ℝ g x = ∑ i ∈ S, (φ i x • innerSL ℝ (ν (p i)) + (h (p i) + inner ℝ (ν (p i)) (x - p i)) • fderiv ℝ (φ i) x) ∧ ∑ i ∈ S, fderiv ℝ (φ i) x = 0 ∧ ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ = ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
