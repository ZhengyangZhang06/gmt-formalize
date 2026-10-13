# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.mollifier_derivative_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-mollifier-derivative-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1`
- Child key: `mollifier_derivative_bound`
- Declaration: `Submission.constancy_mollifier_iteratedFDeriv_norm_le_integral`
- Exact Lean type: `∀ (n : ℕ) (φ : Eucl n → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → ∀ q : ℕ, ∃ C : ℝ, ∀ g : Eucl n → ℝ, Integrable g volume → ∀ x : Eucl n, ‖iteratedFDeriv ℝ q (convolution φ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ C * ∫ y, |g y| ∂volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
