# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.poincare_inequality-a1.mean_deviation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-poincare-inequality-a1-mean-deviation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child key: `mean_deviation`
- Declaration: `Submission.poincare_set_mean_deviation_sq_bound`
- Exact Lean type: `∀ (n : ℕ) (s : Set (Rn n)) (f : Rn n → ℝ), MeasurableSet s → volume s ≠ ∞ → MemLp f 2 (volume.restrict s) → ∫⁻ x in s, ‖f x - ⨍ y in s, f y‖ₑ ^ 2 ≤ (volume s)⁻¹ * ∫⁻ x in s, ∫⁻ y in s, ‖f x - f y‖ₑ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
