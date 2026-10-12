# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.sff_properties-a1.chartwise_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-sff-properties-a1-chartwise-continuity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.sff_properties-a1`
- Child key: `chartwise_continuity`
- Declaration: `Submission.simon_submanifold_continuousOn_of_chart_continuousOn`
- Exact Lean type: `∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (X : Type) [TopologicalSpace X] (F : Rn N → X), Chapter02.IsSimonSubmanifold (E := Rn n) r M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation r M V W ψ → ContinuousOn (fun x ↦ F (ψ x)) V) → ContinuousOn F M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
