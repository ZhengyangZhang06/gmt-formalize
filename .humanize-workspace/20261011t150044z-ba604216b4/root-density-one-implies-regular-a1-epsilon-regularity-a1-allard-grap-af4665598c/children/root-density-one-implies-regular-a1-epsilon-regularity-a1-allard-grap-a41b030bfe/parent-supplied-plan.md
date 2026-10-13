# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-a41b030bfe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child key: `graph_height`
- Declaration: `Submission.dorag_tes_graph_affine_height`
- Exact Lean type: `∀ (n k : ℕ), 0 < n → ∀ (U : Set (Euclid (n + k))) (R : IMRep U n) (ξ : Euclid (n + k)) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (c : Euclid k) (Λ : Euclid n →L[ℝ] Euclid k) (t h₀ : ℝ), 0 < t → 0 ≤ h₀ → Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ᵐ x ∂R.measure, x ∈ closedBall (ξ + ι' c) t → R.mult x = 1) → (∀ x ∈ R.measure.support ∩ closedBall (ξ + ι' c) t, ‖(x - ξ) - T.starProjection (x - ξ)‖ ≤ h₀) → Module.finrank ℝ (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)) = n ∧ (∫⁻ x in closedBall (ξ + ι' c) t, ENNReal.ofReal (‖(x - (ξ + ι' c)) - (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)).starProjection (x - (ξ + ι' c))‖ ^ 2) ∂R.measure) ≤ ENNReal.ofReal (1 + n * 2 ^ n) * (∫⁻ v in ball (0 : Euclid n) t, ENNReal.ofReal (‖f v - c - Λ v‖ ^ 2)) + ENNReal.ofReal ((h₀ + ‖c‖ + ‖Λ‖ * t) ^ 2) * R.measure (closedBall (ξ + ι' c) t \ range (fun v => ξ + ι v + ι' (f v)))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_area-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
