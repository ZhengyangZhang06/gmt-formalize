# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.graph_measure_ext-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-graph-measure-ext-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1`
- Child key: `graph_measure_ext`
- Declaration: `Submission.frt_vgm_eq_map_graph_of_lintegral`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (τ : Euclidean N → Grassmannian N n), Measurable τ → (∀ (A : Set (Euclidean N)) (β : C(Grassmannian N n, ℝ)), MeasurableSet A → (∀ S, 0 ≤ β S) → ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure = ∫⁻ x in A, ENNReal.ofReal (β (τ x)) ∂V.weight) → V.measure = V.weight.map (fun x ↦ (x, τ x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
