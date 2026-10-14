# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-b5ecd87c13/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`
- Child key: `approx_tangent_graph`
- Declaration: `Submission.dgcr_approxTangent_eq_graph_tangent`
- Exact Lean type: `∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s r : ℝ) (A : Set (Euclid (n + k))) (v₀ : Euclid n) (Q : Submodule ℝ (Euclid (n + k))), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → ContDiffOn ℝ 1 u (ball 0 s) → v₀ ∈ ball (0 : Euclid n) s → 0 < r → μHE[n] ((A ∩ ball (z + ι v₀ + ι' (u v₀)) r) \ ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s)) = 0 → HasApproximateTangentSpaceAt n A (z + ι v₀ + ι' (u v₀)) Q → Q = LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v₀ : Euclid n →ₗ[ℝ] Euclid (n + k))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
