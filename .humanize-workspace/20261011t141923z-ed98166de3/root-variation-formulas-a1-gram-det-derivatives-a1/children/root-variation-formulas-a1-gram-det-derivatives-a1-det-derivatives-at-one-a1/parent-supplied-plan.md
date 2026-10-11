# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.gram_det_derivatives-a1.det_derivatives_at_one-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-gram-det-derivatives-a1-det-derivatives-at-one-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1.gram_det_derivatives-a1`
- Child key: `det_derivatives_at_one`
- Declaration: `Submission.variation_matrix_det_derivatives_at_one`
- Exact Lean type: `∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ℝ → Matrix ι ι ℝ), G 0 = 1 → (∀ G₁ : Matrix ι ι ℝ, (∀ i k, HasDerivAt (fun t ↦ G t i k) (G₁ i k) 0) → HasDerivAt (fun t ↦ (G t).det) G₁.trace 0) ∧ ∀ (G' : ℝ → Matrix ι ι ℝ) (G₂ : Matrix ι ι ℝ), (∀ᶠ t in 𝓝 0, ∀ i k, HasDerivAt (fun s ↦ G s i k) (G' t i k) t) → (∀ i k, HasDerivAt (fun t ↦ G' t i k) (G₂ i k) 0) → (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (fun s ↦ (G s).det) t) ∧ HasDerivAt (deriv (fun t ↦ (G t).det)) (G₂.trace + (G' 0).trace ^ 2 - (G' 0 * G' 0).trace) 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
