# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.localized_varifold-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-localized-varifold-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1`
- Child key: `localized_varifold`
- Declaration: `Submission.rsod_exists_localized_varifold`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (B : Set (Amb n ℓ)) (c : ℝ), IsOpen B → B ⊆ U → 0 < c → ∃ W : RectifiableVarifold n ℓ B, W.carrier = V.carrier ∩ B ∧ (∀ x, W.mult x = c * V.mult x) ∧ W.weight = ENNReal.ofReal c • V.weight.restrict B ∧ W.support = B ∩ V.support ∧ (∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → W.HasGeneralizedMeanCurvature H) ∧ (∀ (H : Amb n ℓ → Amb n ℓ) (p : ℝ), V.LocallyLp H p → W.LocallyLp H p)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
