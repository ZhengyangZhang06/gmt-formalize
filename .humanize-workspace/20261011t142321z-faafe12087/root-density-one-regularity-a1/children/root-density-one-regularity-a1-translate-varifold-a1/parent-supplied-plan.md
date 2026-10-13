# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.translate_varifold-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-translate-varifold-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1`
- Child key: `translate_varifold`
- Declaration: `Submission.exists_translated_varifold_allardHypotheses`
- Exact Lean type: `∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ (∀ x, V'.mult x = V.mult (x + ξ)) ∧ V'.weight = V.weight.map (fun x => x - ξ) ∧ V'.support = (fun x => x - ξ) '' V.support ∧ (∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun x => H (x + ξ))) ∧ ∀ (H : Amb n ℓ → Amb n ℓ) (p δ r : ℝ), V.HasGeneralizedMeanCurvature H → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ξ ∈ V.support → 0 < r → closedBall ξ r ⊆ U → V.weight (closedBall ξ r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * r ^ n)) → V.scaledLpNorm H p ξ r ≤ ENNReal.ofReal δ → V'.AllardHypotheses (fun x => H (x + ξ)) p δ r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
