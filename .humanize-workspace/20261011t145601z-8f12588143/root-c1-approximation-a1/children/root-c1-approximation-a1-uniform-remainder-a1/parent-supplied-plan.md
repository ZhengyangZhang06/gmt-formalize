# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_approximation-a1.uniform_remainder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-c1-approximation-a1-uniform-remainder-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_approximation-a1`
- Child key: `uniform_remainder`
- Declaration: `Submission.lipschitz_uniform_remainder_on_closed_subset`
- Exact Lean type: `∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0) (L : Rn n → (Rn n →L[ℝ] ℝ)) (S : Set (Rn n)), LipschitzWith K f → Measurable L → MeasurableSet S → (∀ x ∈ S, HasFDerivAt f (L x) x) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A ⊆ S, IsClosed A ∧ volume (S \ A) < ε ∧ ∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖f y - f x - L x (y - x)‖ ≤ ε' * ‖y - x‖`

## Sibling prerequisites

- `root.c1_approximation-a1.egorov_sigma_finite-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
