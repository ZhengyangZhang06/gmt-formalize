# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1-smooth-annu-922079b7be/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1`
- Child key: `smooth_annulus_estimate`
- Declaration: `Submission.ble_smooth_annulus_estimate`
- Exact Lean type: `∀ n : ℕ, 1 ≤ n → ∀ (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ r s : ℝ, 1 / 2 ≤ r → r < 1 → 0 < s → s ≤ 1 → ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), ‖φ x‖ₑ ^ 2 ≤ ENNReal.ofReal (2 ^ (n + 3) * Real.sqrt (1 - r)) * ((∫⁻ x in ball (0 : Rn n) s, ‖φ x‖ₑ ^ 2) + ∫⁻ x in ball (0 : Rn n) s, ‖gradient φ x‖ₑ ^ 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
