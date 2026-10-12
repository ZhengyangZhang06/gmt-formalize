# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1.kernel_potential-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1-mean-value-kernel-a1-ker-f19d8f8047/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1`
- Child key: `kernel_potential`
- Declaration: `Submission.mvk_exists_kernel_potential`
- Exact Lean type: `∀ n : ℕ, ∃ ρ Ψ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ (∀ z : Rn n, 1 ≤ ‖z‖ → ρ z = 0) ∧ (∀ z : Rn n, 1 ≤ ‖z‖ → Ψ z = 0) ∧ (∀ z : Rn n, ρ (-z) = ρ z) ∧ ∫ z, ρ z = 1 ∧ ∀ z v : Rn n, fderiv ℝ Ψ z v = ρ z * inner ℝ z v`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
