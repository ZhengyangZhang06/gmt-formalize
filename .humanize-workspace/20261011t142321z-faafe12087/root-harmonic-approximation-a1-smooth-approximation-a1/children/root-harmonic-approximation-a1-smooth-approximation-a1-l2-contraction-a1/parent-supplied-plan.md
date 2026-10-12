# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.smooth_approximation-a1.l2_contraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-smooth-approximation-a1-l2-contraction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.smooth_approximation-a1`
- Child key: `l2_contraction`
- Declaration: `Submission.mollifier_l2_contraction`
- Exact Lean type: `∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (ρ : Rn n → ℝ) (H : Rn n → E), Continuous ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → AEStronglyMeasurable H volume → ∫⁻ x, ‖∫ z, ρ z • H (x - z)‖ₑ ^ 2 ≤ ∫⁻ x, ‖H x‖ₑ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
