# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.translate_varifold-a1.gmc_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-translate-varifold-a1-gmc-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.translate_varifold-a1`
- Child key: `gmc_transfer`
- Declaration: `Submission.dohr_tv_gmc_transfer`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U)), V'.weight = V.weight.map (fun x => x - ξ) → (∀ y, V'.tangentProj y = V.tangentProj (y + ξ)) → ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun y => H (y + ξ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
