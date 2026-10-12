# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.whitney_extension-a1.whitney_gluing-a1.derivative_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1-whitney-gluing-a1-derivative-continuity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.whitney_extension-a1.whitney_gluing-a1`
- Child key: `derivative_continuity`
- Declaration: `Submission.whitney_gluing_continuousAt_fderiv`
- Exact Lean type: `∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → 0 ≤ M → (∀ i, p i ∈ A) → (∀ x ∈ A, fderiv ℝ g x = innerSL ℝ (ν x)) → (∀ x ∉ A, ∃ S : Finset ι, (∀ i ∈ S, 0 ≤ φ i x ∧ ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ ∑ i ∈ S, φ i x = 1 ∧ ∑ i ∈ S, fderiv ℝ (φ i) x = 0 ∧ (Metric.infDist x A ≤ 1 → ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) ∧ fderiv ℝ g x = ∑ i ∈ S, (φ i x • innerSL ℝ (ν (p i)) + (h (p i) + inner ℝ (ν (p i)) (x - p i)) • fderiv ℝ (φ i) x)) → ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
