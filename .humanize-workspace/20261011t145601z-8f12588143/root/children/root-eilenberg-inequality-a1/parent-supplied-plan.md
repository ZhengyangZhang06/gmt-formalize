# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.eilenberg_inequality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-eilenberg-inequality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `eilenberg_inequality`
- Declaration: `Submission.eilenberg_upper_integral_inequality`
- Exact Lean type: `∀ (N m k : ℕ), ∃ C : ℝ≥0, ∀ (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μHE[k] (A ∩ f ⁻¹' {y}) ≤ g y) ∧ ∫⁻ y, g y ≤ ((C * L ^ m : ℝ≥0) : ℝ≥0∞) * μHE[m + k] A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
