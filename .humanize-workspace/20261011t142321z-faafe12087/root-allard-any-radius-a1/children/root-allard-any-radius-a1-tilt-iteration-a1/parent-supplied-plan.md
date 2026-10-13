# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.tilt_iteration-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-tilt-iteration-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `tilt_iteration`
- Declaration: `Submission.any_radius_tilt_iteration`
- Exact Lean type: `TiltExcessDecayTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ cl cu : ℝ, 0 < cl → ∃ δ₆ CII CIII : ℝ, 0 < δ₆ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ σ : ℝ), 0 < δ → δ ≤ δ₆ → V.AllardHypotheses H p δ ρ → 0 < σ → σ ≤ δ * ρ / 2 → (∀ s : ℝ, 0 < s → s ≤ σ → cl * unitBallVolume n * s ^ n ≤ (V.weight (closedBall 0 s)).toReal ∧ (V.weight (closedBall 0 s)).toReal ≤ cu * unitBallVolume n * s ^ n) → ∀ S₀ : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S₀ = n → ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧ hsNormSq (S.starProjection - S₀.starProjection) ≤ CII * V.tiltExcessStar H p δ 0 σ S₀ ∧ ∀ s : ℝ, 0 < s → s ≤ σ → V.tiltExcess 0 s S ≤ CIII * (s / σ) ^ (2 * (1 - (n : ℝ) / p)) * V.tiltExcessStar H p δ 0 σ S₀`

## Sibling prerequisites

- `root.allard_any_radius-a1.tangent_ae-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
