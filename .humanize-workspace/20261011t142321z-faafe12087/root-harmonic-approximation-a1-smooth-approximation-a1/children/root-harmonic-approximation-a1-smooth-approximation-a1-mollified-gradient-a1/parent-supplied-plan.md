# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.smooth_approximation-a1.mollified_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-smooth-approximation-a1-mollified-gradient-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.smooth_approximation-a1`
- Child key: `mollified_gradient`
- Declaration: `Submission.w12_ball_mollification_gradient`
- Exact Lean type: `∀ (n : ℕ) (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) → ∀ (ρ : Rn n → ℝ) (ε : ℝ), ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, ε ≤ ‖z‖ → ρ z = 0) → ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ z, ρ z • (ball (0 : Rn n) 1).indicator f (x - z)) ∧ ∀ x : Rn n, ‖x‖ < 1 - ε → gradient (fun x => ∫ z, ρ z • (ball (0 : Rn n) 1).indicator f (x - z)) x = ∫ z, ρ z • (ball (0 : Rn n) 1).indicator g (x - z)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
