# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.graph_measure_ext-a1.finite_measure_ext_continuous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-graph-measure-d5d1bb7324/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1.graph_measure_ext-a1`
- Child key: `finite_measure_ext_continuous`
- Declaration: `Submission.frt_vgm_ext_finite_of_lintegral_continuous`
- Exact Lean type: `∀ (X : Type) [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X] (m₁ m₂ : Measure X), IsFiniteMeasure m₁ → (∀ β : C(X, ℝ), (∀ x, 0 ≤ β x) → ∫⁻ x, ENNReal.ofReal (β x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (β x) ∂m₂) → m₁ = m₂`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
