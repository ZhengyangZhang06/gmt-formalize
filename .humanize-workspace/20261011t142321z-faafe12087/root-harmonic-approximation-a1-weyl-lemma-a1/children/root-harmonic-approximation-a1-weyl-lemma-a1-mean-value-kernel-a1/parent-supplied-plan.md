# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1-mean-value-kernel-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.weyl_lemma-a1`
- Child key: `mean_value_kernel`
- Declaration: `Submission.exists_smooth_mean_value_kernel`
- Exact Lean type: `∀ n : ℕ, 1 ≤ n → ∃ ρ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ z : Rn n, 1 ≤ ‖z‖ → ρ z = 0) ∧ ∀ (h : Rn n → ℝ) (x₀ : Rn n) (t : ℝ), 0 < t → ContDiff ℝ 2 h → (∀ y ∈ closedBall x₀ t, Laplacian.laplacian h y = 0) → ∫ y, t⁻¹ ^ n * ρ (t⁻¹ • y) * h (x₀ - y) = h x₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
