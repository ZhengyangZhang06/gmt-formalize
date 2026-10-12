# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.eilenberg_inequality-a1.compact_fiber_measurable-a1.fiber_content_usc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-eilenberg-inequality-a1-compact-fiber-measurable-a1-fiber-content-usc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.eilenberg_inequality-a1.compact_fiber_measurable-a1`
- Child key: `fiber_content_usc`
- Declaration: `Submission.eilenberg_fiber_open_content_upperSemicontinuous`
- Exact Lean type: `∀ (X : Type) [MetricSpace X] (m : ℕ) (k : ℝ) (δ : ℝ≥0∞) (Q : Set X) (f : X → Rn m), IsCompact Q → ContinuousOn f Q → UpperSemicontinuous (fun y : Rn m ↦ ⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ Metric.ediam (O i) < δ) (_ : Q ∩ f ⁻¹' {y} ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, Metric.ediam (O i) ^ k)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
