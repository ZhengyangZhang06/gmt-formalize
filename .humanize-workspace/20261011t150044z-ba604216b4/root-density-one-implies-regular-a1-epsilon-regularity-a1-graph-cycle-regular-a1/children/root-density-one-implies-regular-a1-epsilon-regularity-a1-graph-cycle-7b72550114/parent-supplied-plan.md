# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-7b72550114/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`
- Child key: `graph_orientation_jacobian`
- Declaration: `Submission.dgcr_graph_orientation_jacobian`
- Exact Lean type: `∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), 0 < n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → ContDiffOn ℝ 1 u (ball 0 s) → ∃ (ξ : Euclid (n + k) → MultiVector (n + k) n) (β : Euclid (n + k) → Covector (Euclid (n + k)) n), ContinuousOn ξ ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) ∧ ContinuousOn β ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) ∧ (∀ x ∈ (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s, ξ x (β x) = 1) ∧ (∀ v ∈ ball (0 : Euclid n) s, IsUnitOrientationOf (ξ (z + ι v + ι' (u v))) (LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v : Euclid n →ₗ[ℝ] Euclid (n + k)))) ∧ ∀ v ∈ ball (0 : Euclid n) s, ∀ α : Covector (Euclid (n + k)) n, α (fun i => fderiv ℝ (fun v => z + ι v + ι' (u v)) v (EuclideanSpace.single i (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => z + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => z + ι v + ι' (u v)) v).det) * ξ (z + ι v + ι' (u v)) α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
