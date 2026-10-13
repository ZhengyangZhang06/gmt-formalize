# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.least_integer_density_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-least-integer-density-point-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1`
- Child key: `least_integer_density_point`
- Declaration: `Submission.rsod_exists_least_integer_density_point`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), (∀ᵐ x ∂V.weight, V.HasDensity x (V.mult x)) → (∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) → ∀ ξ ∈ V.support, ∀ r : ℝ, 0 < r → ∃ (N : ℕ) (x₀ : Amb n ℓ), 1 ≤ N ∧ x₀ ∈ ball ξ r ∧ V.HasDensity x₀ N ∧ ∀ᵐ x ∂V.weight, x ∈ ball ξ r → (N : ℝ) ≤ V.mult x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
