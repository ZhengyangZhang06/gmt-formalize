# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_approximation-a1.remainder_modulus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-approximation-a1-remainder-modulus-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_approximation-a1`
- Child key: `remainder_modulus`
- Declaration: `Submission.c1approx_measurable_remainder_modulus`
- Exact Lean type: `∀ (n : ℕ) (K : ℝ≥0) (C : Set (Rn n)) (f : Rn n → ℝ) (ν : Rn n → Rn n), LipschitzWith K f → Measurable ν → ∃ η : ℕ → Rn n → ℝ, (∀ k, Measurable (η k)) ∧ (∀ k : ℕ, ∀ x ∈ C, ∀ y ∈ C, 0 < ‖y - x‖ → ‖y - x‖ < 1 / ((k : ℝ) + 1) → |f y - f x - inner ℝ (ν x) (y - x)| ≤ η k x * ‖y - x‖) ∧ ∀ x ∈ C, HasFDerivAt f (innerSL ℝ (ν x)) x → Tendsto (fun k ↦ η k x) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
