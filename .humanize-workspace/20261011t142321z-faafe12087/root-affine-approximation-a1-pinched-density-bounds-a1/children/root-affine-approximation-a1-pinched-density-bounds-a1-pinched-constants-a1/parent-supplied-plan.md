# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.pinched_density_bounds-a1.pinched_constants-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-pinched-density-bounds-a1-pinched-constants-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.pinched_density_bounds-a1`
- Child key: `pinched_constants`
- Declaration: `Submission.aal_pinched_constants`
- Exact Lean type: `∀ (n : ℕ) (κ ω : ℝ), 0 < κ → 0 < ω → ∃ Cp δp : ℝ, 1 ≤ Cp ∧ 0 < δp ∧ δp ≤ 1 / 8 ∧ δp ≤ κ ∧ Cp * δp ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ δp → Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 4 * t) ^ n * ω) + 2 * Real.exp (t / κ) * (t / κ) ≤ (1 + Cp * t) * ω ∧ (1 - Cp * t) * ω ≤ Real.exp (-(t / κ)) * (ω - t / κ) ∧ Real.exp (t / κ) * (Real.exp (t / κ) * ((1 + t) / (1 - 4 * t) ^ n * ω) + t / κ - ω) ≤ Cp * ω * t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
