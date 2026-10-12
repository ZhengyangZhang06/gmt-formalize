# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.bv_results-a1.compactness-a1.convolution_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-compactness-a1-convolution-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.bv_results-a1.compactness-a1`
- Child key: `convolution_bounds`
- Declaration: `Submission.bv_convolution_bound_and_lipschitz`
- Exact Lean type: `∀ (n : ℕ) (ρ F : Rn n → ℝ) (A : ℝ) (K : ℝ≥0), (∀ x, |ρ x| ≤ A) → LipschitzWith K ρ → Integrable F volume → ∀ x y : Rn n, |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x| ≤ A * (∫ t, |F t|) ∧ |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume y| ≤ K * ‖x - y‖ * (∫ t, |F t|)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
