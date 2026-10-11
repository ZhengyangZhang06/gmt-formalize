# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.eilenberg_inequality-a1.compact_fiber_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-eilenberg-inequality-a1-compact-fiber-measurable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.eilenberg_inequality-a1`
- Child key: `compact_fiber_measurable`
- Declaration: `Submission.eilenberg_compact_fiber_measurable`
- Exact Lean type: `∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (k : ℝ) (Q : Set X) (f : X → Rn m), 0 < k → IsCompact Q → ContinuousOn f Q → Measurable (fun y ↦ Chapter01.simonHausdorffMeasureReal k (Q ∩ f ⁻¹' {y}))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
