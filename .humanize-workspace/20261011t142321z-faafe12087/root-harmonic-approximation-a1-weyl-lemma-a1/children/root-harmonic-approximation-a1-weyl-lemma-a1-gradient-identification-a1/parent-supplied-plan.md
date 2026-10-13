# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.weyl_lemma-a1.gradient_identification-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1-gradient-identification-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.weyl_lemma-a1`
- Child key: `gradient_identification`
- Declaration: `Submission.w12_ball_gradient_ae_eq_of_contDiffAt`
- Exact Lean type: `∀ n : ℕ, 1 ≤ n → ∀ (w u : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient w g (ball 0 1) → (∀ x ∈ ball (0 : Rn n) 1, ContDiffAt ℝ 1 u x) → (∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) 1)), u x = w x) → ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) 1)), gradient u x = g x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
