# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.height_bound_small_delta-a1.normal_part_conical_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-height-bound-small-delta-a1-normal-part-b310d9c960/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.height_bound_small_delta-a1`
- Child key: `normal_part_conical_bound`
- Declaration: `Submission.aal_normal_sq_lintegral_le_conical`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (P : Amb n ℓ → Amb n ℓ →L[ℝ] Amb n ℓ) (y : Amb n ℓ) (s : ℝ), 0 < s → ∫⁻ x in closedBall y s, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2) ∂μ ≤ ENNReal.ofReal (s ^ (n + 2)) * ∫⁻ x in closedBall y s, ENNReal.ofReal (‖(x - y) - P x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
