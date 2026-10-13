# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.chart_pieces-a1.first_order_agreement-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-chart-pieces-a1-first-order-agreement-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.chart_pieces-a1`
- Child key: `first_order_agreement`
- Declaration: `Submission.lipschitzOn_open_c1_first_order_agreement`
- Exact Lean type: `∀ (n m : ℕ), (∀ (F : Rn n → Rn m) (K : ℝ≥0), LipschitzWith K F → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → Rn m, ContDiff ℝ 1 g ∧ volume {x | F x ≠ g x ∨ fderiv ℝ F x ≠ fderiv ℝ g x} < ε) → ∀ (D : Set (Rn n)) (h : Rn n → Rn m), IsOpen D → (∃ K, LipschitzOnWith K h D) → ∃ (G : ℕ → Rn n → Rn m) (E : ℕ → Set (Rn n)), (∀ i, ContDiff ℝ 1 (G i)) ∧ (∀ i, MeasurableSet (E i)) ∧ (∀ i, E i ⊆ D) ∧ (∀ i, ∀ u ∈ E i, h u = G i u ∧ HasFDerivAt h (fderiv ℝ (G i) u) u) ∧ volume (D \ ⋃ i, E i) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
