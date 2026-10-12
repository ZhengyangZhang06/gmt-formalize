# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.weyl_lemma-a1.local_representative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1-local-representative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.weyl_lemma-a1`
- Child key: `local_representative`
- Declaration: `Submission.ball_weakly_harmonic_local_representative`
- Exact Lean type: `∀ n : ℕ, 1 ≤ n → ∀ w : Rn n → ℝ, IntegrableOn w (ball (0 : Rn n) 1) → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 → ∫ x in ball (0 : Rn n) 1, w x * Laplacian.laplacian ζ x = 0) → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ v : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd v (ball (0 : Rn n) (1 - ε)) ∧ ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) (1 - 2 * ε))), v x = w x`

## Sibling prerequisites

- `root.harmonic_approximation-a1.weyl_lemma-a1.mollifier_harmonic-a1`
- `root.harmonic_approximation-a1.weyl_lemma-a1.mean_value_kernel-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
