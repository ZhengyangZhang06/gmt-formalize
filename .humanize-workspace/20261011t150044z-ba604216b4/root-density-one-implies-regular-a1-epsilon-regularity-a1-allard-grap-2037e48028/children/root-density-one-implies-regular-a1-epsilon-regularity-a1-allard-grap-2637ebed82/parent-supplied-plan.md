# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.graph_plane_pointwise-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2637ebed82/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1`
- Child key: `graph_plane_pointwise`
- Declaration: `Submission.dorag_tes_gv_graph_plane_pointwise`
- Exact Lean type: `∀ (n k : ℕ) (T Q : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (L : Euclid n →L[ℝ] Euclid k) (j : Fin k) (t : ℝ), Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → Q = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ L.toLinearMap) → ‖L‖ ≤ 1 → 0 ≤ t → (∀ a b : Euclid (n + k), a ∈ T → b ∈ T → |inner ℝ (Q.starProjection a) b - inner ℝ a b| ≤ t * ‖a‖ * ‖b‖) → (∀ e : Euclid (n + k), e ∈ Tᗮ → ‖Q.starProjection e‖ ^ 2 ≤ t * ‖e‖ ^ 2) → ‖(EuclideanSpace.proj j).comp L‖ ^ 2 ≤ 2 * t ∧ ∀ m : Euclid n →L[ℝ] ℝ, |m (P (Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))))) - ∑ i : Fin n, ((EuclideanSpace.proj j).comp L) (EuclideanSpace.single i (1 : ℝ)) * m (EuclideanSpace.single i (1 : ℝ))| ≤ t * ‖m‖`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.adapted_frame-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
