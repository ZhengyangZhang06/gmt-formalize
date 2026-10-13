# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1.ray_inequality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1-smooth-annu-51aa63490f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1`
- Child key: `ray_inequality`
- Declaration: `Submission.ble_sac_ray_sq_bound`
- Exact Lean type: `∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ (x : Rn n), ‖x‖ ≤ 1 → ∀ τ : ℝ, τ ≤ 1 → ENNReal.ofReal (1 - τ) * ‖φ x‖ₑ ^ 2 ≤ 2 * (∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) + 2 * ENNReal.ofReal ((1 - τ) ^ 2) * ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
