# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1.radial_ibp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1-mean-value-kernel-a1-radial-ibp-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1`
- Child key: `radial_ibp`
- Declaration: `Submission.mvk_integral_radial_fderiv_eq_neg_laplacian`
- Exact Lean type: `∀ (n : ℕ) (ρ Ψ h : Rn n → ℝ) (x₀ : Rn n) (σ : ℝ), σ ≠ 0 → ContDiff ℝ 2 h → ContDiff ℝ 1 Ψ → (∀ z : Rn n, 1 ≤ ‖z‖ → Ψ z = 0) → (∀ z v : Rn n, fderiv ℝ Ψ z v = ρ z * inner ℝ z v) → ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z = -σ * ∫ z, Laplacian.laplacian h (x₀ + σ • z) * Ψ z`

## Sibling prerequisites

- `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1.green_identity-a1`
- `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1.laplacian_rescale-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
