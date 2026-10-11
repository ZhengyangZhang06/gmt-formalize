# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.allard_scale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-allard-scale-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1`
- Child key: `allard_scale`
- Declaration: `Submission.density_one_allard_scale`
- Exact Lean type: `∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (δ : ℝ), IsOpen U → (n : ℝ) < p → V.LocallyLp H p → ξ ∈ U → V.HasDensity ξ 1 → 0 < δ → ξ ∈ V.support ∧ ∃ r : ℝ, 0 < r ∧ closedBall ξ r ⊆ U ∧ V.weight (closedBall ξ r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * r ^ n)) ∧ V.scaledLpNorm H p ξ r ≤ ENNReal.ofReal δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
