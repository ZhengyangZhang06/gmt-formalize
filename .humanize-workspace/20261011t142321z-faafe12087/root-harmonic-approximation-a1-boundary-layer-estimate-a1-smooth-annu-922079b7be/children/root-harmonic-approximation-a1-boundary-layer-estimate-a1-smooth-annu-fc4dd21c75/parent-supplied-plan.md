# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1.annulus_kernel_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1-smooth-annu-fc4dd21c75/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1`
- Child key: `annulus_kernel_bound`
- Declaration: `Submission.ble_sac_annulus_dilation_avg_le`
- Exact Lean type: `∀ (n : ℕ) (F : Rn n → ℝ≥0∞), Measurable F → ∀ r s τ : ℝ, 1 / 2 ≤ r → r < 1 → 0 < s → 1 / 2 ≤ τ → ∫⁻ t in Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x) ≤ ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) * ∫⁻ y in ball (0 : Rn n) s, F y`

## Sibling prerequisites

- `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1.dilation_formula-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
