# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db45a55178/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Child key: `graph_c1`
- Declaration: `Submission.dorag_graph_c1_of_tilt_decay`
- Exact Lean type: `∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (z : Euclid (n + k)) (a s₀ K : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ 1 / 4 * ‖v - w‖) → f 0 = 0 → 0 < a → 0 < s₀ → closedBall z a ⊆ W → R.measure.support ∩ closedBall z a = range (fun v => z + ι v + ι' (f v)) ∩ closedBall z a → (∀ ξ ∈ R.measure.support ∩ closedBall z a, ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall ξ s, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (K * s ^ (n + 1))) → ContDiffOn ℝ 1 f (ball (0 : Euclid n) (a / 2))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tangent_projection_measurable-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.support_null-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
