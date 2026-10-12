# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.tangent_projection_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-tangent-projection-extension-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1`
- Child key: `tangent_projection_extension`
- Declaration: `Submission.submanifold_tangentProjection_c1_extension`
- Exact Lean type: `∀ (P d : ℕ) (N : Set (Euclid P)), IsEmbeddedSubmanifold 2 d N → ∃ (O : Set (Euclid P)) (pr : Euclid P → (Euclid P →L[ℝ] Euclid P)), IsOpen O ∧ N ⊆ O ∧ ContDiffOn ℝ 1 pr O ∧ ∀ z ∈ N, pr z = (Submodule.span ℝ (tangentSpace N z)).starProjection`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
