# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.approx_tangent_in_submanifold-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1`
- Child key: `approx_tangent_in_submanifold`
- Declaration: `Submission.approxTangent_le_submanifold_tangentSpace`
- Exact Lean type: `∀ (P n d : ℕ) (N M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), IsEmbeddedSubmanifold 1 d N → x ∈ N → μHE[n] (M \ N) = 0 → HasApproximateTangentSpaceAt n M x Q → (Q : Set (Euclid P)) ⊆ tangentSpace N x`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
