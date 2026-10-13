# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.density_constants-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-density-constants-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1`
- Child key: `density_constants`
- Declaration: `Submission.allard52_density_constants`
- Exact Lean type: `∀ (n : ℕ) (κ ω : ℝ), 0 < κ → 0 < ω → ∃ δP CP : ℝ, 0 < δP ∧ δP ≤ 1 / 8 ∧ δP ≤ κ ∧ 0 < CP ∧ CP * δP ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ δP → Real.exp (2 * (t / κ)) * ((1 + t) / (1 - 3 * t) ^ n * ω) + 2 * Real.exp (t / κ) * (t / κ) ≤ (1 + CP * t) * ω ∧ (1 - CP * t) * ω ≤ Real.exp (-(t / κ)) * (ω - t / κ) ∧ Real.exp (t / κ) * (Real.exp (t / κ) * ((1 + t) / (1 - 3 * t) ^ n * ω) + t / κ - ω) ≤ CP * ω * t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
