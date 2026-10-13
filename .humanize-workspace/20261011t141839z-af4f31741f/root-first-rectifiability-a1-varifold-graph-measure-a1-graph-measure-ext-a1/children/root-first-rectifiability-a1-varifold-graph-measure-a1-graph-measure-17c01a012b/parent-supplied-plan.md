# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.graph_measure_ext-a1.prod_measure_ext_rectangles-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-graph-measure-17c01a012b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1.graph_measure_ext-a1`
- Child key: `prod_measure_ext_rectangles`
- Declaration: `Submission.frt_vgm_ext_prod_of_finite_rectangles`
- Exact Lean type: `∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ρ₁ ρ₂ : Measure (X × Y)), SigmaFinite μ → (∀ A : Set X, MeasurableSet A → μ A ≠ ∞ → ρ₁ (A ×ˢ (univ : Set Y)) ≠ ∞) → (∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B → μ A ≠ ∞ → ρ₁ (A ×ˢ B) = ρ₂ (A ×ˢ B)) → ρ₁ = ρ₂`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
