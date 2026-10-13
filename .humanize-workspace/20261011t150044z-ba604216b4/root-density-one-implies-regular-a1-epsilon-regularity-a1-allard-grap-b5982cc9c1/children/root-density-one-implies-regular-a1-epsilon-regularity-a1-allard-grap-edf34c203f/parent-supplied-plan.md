# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1.energy_inequality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-edf34c203f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1`
- Child key: `energy_inequality`
- Declaration: `Submission.dorag_th_tilt_energy_inequality`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (S : Submodule ℝ (Euclid P)) (ξ : Euclid P) (ζ : Euclid P → ℝ), W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → Module.finrank ℝ S = n → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ W → ∫⁻ x, ENNReal.ofReal (ζ x ^ 2 * ∑ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure + ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖) ∂R.measure`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1.projection_trace-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1.hs_operator_bound-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1.test_field_divergence-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
