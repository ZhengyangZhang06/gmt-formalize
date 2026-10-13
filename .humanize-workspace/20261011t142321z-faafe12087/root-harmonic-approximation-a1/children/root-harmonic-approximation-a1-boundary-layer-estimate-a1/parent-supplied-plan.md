# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.boundary_layer_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1`
- Child key: `boundary_layer_estimate`
- Declaration: `Submission.w12_ball_boundary_layer_estimate`
- Exact Lean type: `∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) → ∀ r : ℝ, 0 < r → r < 1 → ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal (C * Real.sqrt (1 - r)) * ((∫⁻ x in ball (0 : Rn n) 1, ‖f x‖ₑ ^ 2) + ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2)`

## Sibling prerequisites

- `root.harmonic_approximation-a1.smooth_approximation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
