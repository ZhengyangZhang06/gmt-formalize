# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.tangent_graph_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-constancy-a1-tangent-graph-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1`
- Child key: `tangent_graph_measure`
- Declaration: `Submission.stationary_constancy_tangentGraph_measure`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)), V.Stationary → Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M → U ∩ V.weight.support ⊆ M → IsPreconnected (M ∩ U) → M.Nonempty → ∃ (c : ℝ≥0∞) (T : Euclidean N → Grassmannian N n), c ≠ ∞ ∧ Measurable T ∧ V.measure = (c • (μHE[n] : Measure (Euclidean N)).restrict (M ∩ U)).map (fun x ↦ (x, T x)) ∧ (c ≠ 0 → ∀ x ∈ M ∩ U, ((T x).plane : Set (Euclidean N)) = classicalTangentSpace M x)`

## Sibling prerequisites

- `root.constancy-a1.classical_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
