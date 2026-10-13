# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-b5982cc9c1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Child key: `tilt_height`
- Declaration: `Submission.dorag_tilt_height_estimate`
- Exact Lean type: `∀ (n k : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ξ : Euclid (n + k)) (r : ℝ) (S : Submodule ℝ (Euclid (n + k))), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → 0 < r → closedBall ξ r ⊆ W → Module.finrank ℝ S = n → ∫⁻ x in closedBall ξ (r / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal C * (ENNReal.ofReal (1 / r ^ 2) * ∫⁻ x in closedBall ξ r, ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure + ENNReal.ofReal (κ ^ 2 * r ^ 2) * R.measure (closedBall ξ r))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tangent_projection_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
