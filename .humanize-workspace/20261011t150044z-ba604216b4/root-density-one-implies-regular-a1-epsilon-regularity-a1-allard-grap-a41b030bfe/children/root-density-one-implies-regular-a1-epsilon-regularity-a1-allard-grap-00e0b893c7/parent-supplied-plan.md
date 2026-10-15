# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1.plane_frame-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-00e0b893c7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1`
- Child key: `plane_frame`
- Declaration: `Submission.dorag_tes_gah_plane_frame_bounds`
- Exact Lean type: `∀ (n k : ℕ) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (Λ : Euclid n →L[ℝ] Euclid k) (ξ : Euclid (n + k)) (c : Euclid k), Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → Module.finrank ℝ (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)) = n ∧ (∀ (v : Euclid n) (w : Euclid k), ‖(ξ + ι v + ι' w - (ξ + ι' c)) - (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)).starProjection (ξ + ι v + ι' w - (ξ + ι' c))‖ ≤ ‖w - c - Λ v‖ ∧ ‖v‖ ≤ ‖ξ + ι v + ι' w - (ξ + ι' c)‖) ∧ ∀ x : Euclid (n + k), ‖(x - (ξ + ι' c)) - (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)).starProjection (x - (ξ + ι' c))‖ ≤ ‖(x - ξ) - T.starProjection (x - ξ)‖ + ‖c‖ + ‖Λ‖ * ‖x - (ξ + ι' c)‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
