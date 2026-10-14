# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-5d86c28dbf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`
- Child key: `boundary_weak_derivatives`
- Declaration: `Submission.dgcr_graph_boundary_weak_derivatives`
- Exact Lean type: `∀ (n k : ℕ) (U : Set (Euclid (n + k))) (T : GeometricCurrentOn U n) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s h : ℝ) (G : Euclid n → ℝ), 0 < n → BoundaryVanishes T → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → 0 < h → ContDiffOn ℝ 1 u (ball 0 s) → (∀ v ∈ ball (0 : Euclid n) s, u v ∈ ball (0 : Euclid k) h) → {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ⊆ U → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid (n + k)) n) ⊆ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} → T ω = ∫ v in ball (0 : Euclid n) s, G v * (ω : DifferentialForm (Euclid (n + k)) n) (z + ι v + ι' (u v)) (fun i => fderiv ℝ (fun v => z + ι v + ι' (u v)) v (EuclideanSpace.single i (1 : ℝ)))) → ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → tsupport a ⊆ ball (0 : Euclid n) s → ∀ j : Fin n, ∫ v in ball (0 : Euclid n) s, G v * fderiv ℝ a v (EuclideanSpace.single j (1 : ℝ)) = 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.orthogonal_coordinates-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
