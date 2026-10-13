# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1.laplacian_rescale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1-mean-value-kernel-a1-lap-4f51451e66/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1`
- Child key: `laplacian_rescale`
- Declaration: `Submission.mvk_laplacian_comp_add_smul`
- Exact Lean type: `∀ (n : ℕ) (h : Rn n → ℝ) (x₀ : Rn n) (σ : ℝ), ContDiff ℝ 2 h → ∀ z : Rn n, Laplacian.laplacian (fun y => h (x₀ + σ • y)) z = σ ^ 2 * Laplacian.laplacian h (x₀ + σ • z)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
