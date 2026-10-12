# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.gram_det_derivatives-a1.sqrt_derivatives_at_one-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-gram-det-derivatives-a1-sqrt-derivatives-at-one-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.gram_det_derivatives-a1`
- Child key: `sqrt_derivatives_at_one`
- Declaration: `Submission.variation_sqrt_derivatives_at_one`
- Exact Lean type: `∀ (h : ℝ → ℝ) (h₁ : ℝ), h 0 = 1 → HasDerivAt h h₁ 0 → HasDerivAt (fun t ↦ Real.sqrt (h t)) (h₁ / 2) 0 ∧ ∀ h₂ : ℝ, (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ h t) → HasDerivAt (deriv h) h₂ 0 → HasDerivAt (deriv (fun t ↦ Real.sqrt (h t))) (h₂ / 2 - h₁ ^ 2 / 4) 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
