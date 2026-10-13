# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.rectifiable_hausdorff-a1.measure_le_hausdorff-a1.closed_ball_covering_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-rectifiable-hausdorff-a1-measure-le-hausdorff-a1-cl-58fb6e8809/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.rectifiable_hausdorff-a1.measure_le_hausdorff-a1`
- Child key: `closed_ball_covering_bound`
- Declaration: `Submission.deGiorgiRH_measure_le_mul_hausdorffMeasure_of_closedBall_le`
- Exact Lean type: `∀ (n N : ℕ) (μ : Measure (Rn N)) (B : Set (Rn N)) (c : ℝ≥0∞) (δ : ℝ), c ≠ 0 → c ≠ ∞ → 0 < δ → (∀ x ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ (Metric.closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ n)) → μ B ≤ c * μH[(n : ℝ)] B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
