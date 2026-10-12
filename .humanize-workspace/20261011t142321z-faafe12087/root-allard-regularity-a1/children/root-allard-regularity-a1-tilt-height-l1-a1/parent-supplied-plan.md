# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.tilt_height_l1-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-tilt-height-l1-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1`
- Child key: `tilt_height_l1`
- Declaration: `Submission.allard52_tilt_height_l1`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (z : Amb n ℓ) (r h : ℝ), 0 < r → 0 ≤ h → closedBall z r ⊆ U → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → (∀ x ∈ V.support ∩ closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ≤ h) → ∫ x in closedBall z (r / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤ C * (r ^ 2)⁻¹ * ∫ x in closedBall z r, infDist (x - z) (T : Set (Amb n ℓ)) ^ 2 ∂V.weight + C * h * ∫ x in closedBall z r, ‖H x‖ ∂V.weight`

## Sibling prerequisites

- `root.allard_regularity-a1.tangent_ae-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
