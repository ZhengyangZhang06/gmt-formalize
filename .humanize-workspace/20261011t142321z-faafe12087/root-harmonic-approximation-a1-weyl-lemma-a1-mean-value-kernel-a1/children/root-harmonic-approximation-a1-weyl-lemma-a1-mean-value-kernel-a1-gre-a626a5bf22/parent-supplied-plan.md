# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1.green_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1-mean-value-kernel-a1-gre-a626a5bf22/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1`
- Child key: `green_identity`
- Declaration: `Submission.mvk_integral_fderiv_grad_eq_neg_laplacian`
- Exact Lean type: `∀ (n : ℕ) (H Ψ : Rn n → ℝ) (w : Rn n → Rn n), ContDiff ℝ 2 H → ContDiff ℝ 1 Ψ → HasCompactSupport Ψ → (∀ z v : Rn n, fderiv ℝ Ψ z v = inner ℝ (w z) v) → ∫ z, fderiv ℝ H z (w z) = -∫ z, Laplacian.laplacian H z * Ψ z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
