# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.translate_varifold-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-translate-varifold-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1`
- Child key: `translate_varifold`
- Declaration: `Submission.ted_translate_varifold`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x + ξ) ⁻¹' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ V'.weight = V.weight.map (fun x => x - ξ) ∧ (∀ x, V'.mult x = V.mult (x + ξ)) ∧ (∀ x, V'.tangentProj x = V.tangentProj (x + ξ)) ∧ (∀ x, x ∈ V'.support ↔ x + ξ ∈ V.support) ∧ (∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun x => H (x + ξ))) ∧ (∀ (z : Amb n ℓ) (s : ℝ) (S : Submodule ℝ (Amb n ℓ)), V'.tiltExcess z s S = V.tiltExcess (z + ξ) s S) ∧ (∀ (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (z : Amb n ℓ) (s : ℝ), V'.scaledLpNorm (fun x => H (x + ξ)) p z s = V.scaledLpNorm H p (z + ξ) s)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
