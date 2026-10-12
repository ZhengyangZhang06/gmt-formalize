# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_approximation-a1.bounded_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-bounded-extension-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_approximation-a1`
- Child key: `bounded_extension`
- Declaration: `Submission.lip_approx_bounded_extension`
- Exact Lean type: `∀ (n ℓ : ℕ) (A : Set (Rn n)) (g : Rn n → Rn ℓ) (M R₀ : ℝ), 0 ≤ M → 0 ≤ R₀ → (∀ x ∈ A, ∀ z ∈ A, ‖g x - g z‖ ≤ M * ‖x - z‖) → (∀ x ∈ A, ‖g x‖ ≤ R₀) → ∃ f : Rn n → Rn ℓ, (∀ x ∈ A, f x = g x) ∧ (∀ x z, ‖f x - f z‖ ≤ Real.sqrt ℓ * M * ‖x - z‖) ∧ ∀ x, ‖f x‖ ≤ R₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
