# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_graph_cover-a1.dim_zero_countable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1-dim-zero-countable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_graph_cover-a1`
- Child key: `dim_zero_countable`
- Declaration: `Submission.tgc_dim_zero_tangent_points_countable`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Euclidean N)) (V : Varifold N 0 U), {x : Euclidean N | ∃ (T : Grassmannian N 0) (θ : ℝ), HasTangentPlane V x T θ}.Countable`

## Sibling prerequisites

- `root.tangent_graph_cover-a1.lower_mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
