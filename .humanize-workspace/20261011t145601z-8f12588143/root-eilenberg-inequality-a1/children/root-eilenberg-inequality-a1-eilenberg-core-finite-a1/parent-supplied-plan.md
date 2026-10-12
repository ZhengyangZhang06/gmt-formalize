# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.eilenberg_inequality-a1.eilenberg_core_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-eilenberg-inequality-a1-eilenberg-core-finite-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.eilenberg_inequality-a1`
- Child key: `eilenberg_core_finite`
- Declaration: `Submission.eilenberg_hausdorff_upper_integral_of_ne_top`
- Exact Lean type: `∀ (N m k : ℕ) (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f → μH[((m + k : ℕ) : ℝ)] A ≠ ∞ → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μH[(k : ℝ)] (A ∩ f ⁻¹' {y}) ≤ g y) ∧ ∫⁻ y, g y ≤ volume (Metric.ball (0 : Rn m) 1) * (L : ℝ≥0∞) ^ m * μH[((m + k : ℕ) : ℝ)] A`

## Sibling prerequisites

- `root.eilenberg_inequality-a1.hausdorff_near_optimal_cover-a1`
- `root.eilenberg_inequality-a1.volume_diameter_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
