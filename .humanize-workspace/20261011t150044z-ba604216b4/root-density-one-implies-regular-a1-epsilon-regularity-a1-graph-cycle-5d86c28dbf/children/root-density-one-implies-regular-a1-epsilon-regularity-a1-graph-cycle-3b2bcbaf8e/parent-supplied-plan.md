# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.graph_pullback_extderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-3b2bcbaf8e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1`
- Child key: `graph_pullback_extderiv`
- Declaration: `Submission.dgcr_bwd_graph_pullback_extDeriv`
- Exact Lean type: `∀ (m k : ℕ) (ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid (m + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + 1 + k)) (u : Euclid (m + 1) → Euclid k) (z : Euclid (m + 1 + k)) (ψ : DifferentialForm (Euclid (m + 1)) m) (v : Euclid (m + 1)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsSmoothForm ψ → DifferentiableAt ℝ u v → exteriorDerivative (affinePullbackForm (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) (-(ContinuousLinearMap.adjoint ι.toContinuousLinearMap z)) ψ) (z + ι v + ι' (u v)) (fun i => fderiv ℝ (fun v => z + ι v + ι' (u v)) v (EuclideanSpace.single i (1 : ℝ))) = exteriorDerivative ψ v (fun i => EuclideanSpace.single i (1 : ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
