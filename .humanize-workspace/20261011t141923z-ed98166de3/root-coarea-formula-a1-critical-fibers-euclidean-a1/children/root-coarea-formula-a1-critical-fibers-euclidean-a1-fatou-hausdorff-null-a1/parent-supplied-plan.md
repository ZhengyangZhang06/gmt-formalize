# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.critical_fibers_euclidean-a1.fatou_hausdorff_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1-fatou-hausdorff-null-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.critical_fibers_euclidean-a1`
- Child key: `fatou_hausdorff_null`
- Declaration: `Submission.ae_hausdorffMeasure_fiber_eq_zero_of_small_ball_covers`
- Exact Lean type: `∀ (X Y : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] (ν : Measure Y) (k : ℕ) (K : Set X) (G : X → Y), (∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ (s : Finset X) (r : ℝ), 0 < r ∧ 2 * r ≤ δ ∧ K ⊆ ⋃ x ∈ s, closedBall x r ∧ ∑ x ∈ s, ENNReal.ofReal ((2 * r) ^ k) * ν (G '' closedBall x r) ≤ ENNReal.ofReal ε) → ∀ᵐ y ∂ν, μH[k] (K ∩ G ⁻¹' {y}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
