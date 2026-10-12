# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1.graph_image_flat-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-e94f5706c0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1`
- Child key: `graph_image_flat`
- Declaration: `Submission.dgcr_atg_graph_image_flat`
- Exact Lean type: `∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (D : Set (Euclid n)) (v₀ : Euclid n), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → DifferentiableAt ℝ u v₀ → ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ (fun v => z + ι v + ι' (u v)) '' D, dist y (z + ι v₀ + ι' (u v₀)) < ρ → ∃ t ∈ LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v₀ : Euclid n →ₗ[ℝ] Euclid (n + k)), ‖y - (z + ι v₀ + ι' (u v₀)) - t‖ ≤ ε * ‖y - (z + ι v₀ + ι' (u v₀))‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
