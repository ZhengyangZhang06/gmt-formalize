# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.eilenberg_inequality-a1.hausdorff_near_optimal_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-eilenberg-inequality-a1-hausdorff-near-optimal-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.eilenberg_inequality-a1`
- Child key: `hausdorff_near_optimal_cover`
- Declaration: `Submission.hausdorffMeasure_exists_cover_tsum_le_add`
- Exact Lean type: `∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (d : ℝ) (s : Set X) (r ε : ℝ≥0∞), 0 < r → ε ≠ 0 → μH[d] s ≠ ∞ → ∃ t : ℕ → Set X, s ⊆ ⋃ n, t n ∧ (∀ n, Metric.ediam (t n) ≤ r) ∧ ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d ≤ μH[d] s + ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
