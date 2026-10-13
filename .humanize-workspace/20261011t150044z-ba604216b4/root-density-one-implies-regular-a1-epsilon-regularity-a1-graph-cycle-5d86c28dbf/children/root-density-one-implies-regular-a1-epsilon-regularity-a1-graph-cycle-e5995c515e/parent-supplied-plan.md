# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.graph_cutoff_lift-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-e5995c515e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1`
- Child key: `graph_cutoff_lift`
- Declaration: `Submission.dgcr_bwd_graph_cutoff_lift`
- Exact Lean type: `∀ (m k : ℕ) (U : Set (Euclid (m + 1 + k))) (ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid (m + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + 1 + k)) (u : Euclid (m + 1) → Euclid k) (z : Euclid (m + 1 + k)) (s h : ℝ) (ψ : DifferentialForm (Euclid (m + 1)) m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ x : Euclid (m + 1 + k), ∃ v : Euclid (m + 1), ∃ w : Euclid k, x = ι v + ι' w) → 0 < h → ContinuousOn u (ball 0 s) → (∀ v ∈ ball (0 : Euclid (m + 1)) s, u v ∈ ball (0 : Euclid k) h) → {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ⊆ U → IsSmoothForm ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid (m + 1)) s → ∃ φ : TestFormOn U m, tsupport (φ : DifferentialForm (Euclid (m + 1 + k)) m) ⊆ {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ∧ ∀ v ∈ ball (0 : Euclid (m + 1)) s, (φ : DifferentialForm (Euclid (m + 1 + k)) m) =ᶠ[𝓝 (z + ι v + ι' (u v))] affinePullbackForm (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) (-(ContinuousLinearMap.adjoint ι.toContinuousLinearMap z)) ψ`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.normal_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
