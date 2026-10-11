# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.poincare_inequality-a1.kernel_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-poincare-inequality-a1-kernel-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.poincare_inequality-a1`
- Child key: `kernel_bound`
- Declaration: `Submission.closedBall_rpow_kernel_lintegral_le_of_growth`
- Exact Lean type: `∀ {X : Type} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (n : ℕ) (y : X) (ρ K : ℝ), 0 < n → (∀ s : ℝ, 0 < s → s ≤ ρ → μ (closedBall y s) ≤ ENNReal.ofReal (K * s ^ n)) → ∀ s : ℝ, 0 < s → s ≤ ρ → ∫⁻ x in closedBall y s, ENNReal.ofReal (‖x - y‖ ^ (1 - (n : ℝ))) ∂μ ≤ ENNReal.ofReal (n * K * s)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
