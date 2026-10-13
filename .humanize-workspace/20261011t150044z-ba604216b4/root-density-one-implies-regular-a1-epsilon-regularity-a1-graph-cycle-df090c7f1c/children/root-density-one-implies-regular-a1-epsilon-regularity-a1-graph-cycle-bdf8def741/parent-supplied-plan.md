# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_embedded-a1.left_inverse_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-bdf8def741/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_embedded-a1`
- Child key: `left_inverse_tangent`
- Declaration: `Submission.dgce_left_inverse_tangentSpace_eq_range`
- Exact Lean type: `∀ (d P : ℕ) (Φ : Euclid d → Euclid P) (L : Euclid P →L[ℝ] Euclid d) (z : Euclid P) (s : ℝ), ContDiffOn ℝ 1 Φ (ball 0 s) → (∀ v ∈ ball (0 : Euclid d) s, L (Φ v - z) = v) → ∀ v ∈ ball (0 : Euclid d) s, tangentSpace (Φ '' ball (0 : Euclid d) s) (Φ v) = (LinearMap.range (fderiv ℝ Φ v : Euclid d →ₗ[ℝ] Euclid P) : Set (Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
