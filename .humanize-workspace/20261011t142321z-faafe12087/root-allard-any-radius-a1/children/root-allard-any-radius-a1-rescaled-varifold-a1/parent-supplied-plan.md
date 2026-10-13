# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.rescaled_varifold-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-rescaled-varifold-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `rescaled_varifold`
- Declaration: `Submission.any_radius_rescaled_varifold`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (c : Amb n ℓ) (R : ℝ), 0 < R → ∃ V' : RectifiableVarifold n ℓ ((fun x => c + R • x) ⁻¹' U), V'.carrier = (fun x => c + R • x) ⁻¹' V.carrier ∧ (∀ x, V'.mult x = V.mult (c + R • x)) ∧ V'.weight = (ENNReal.ofReal (R ^ n))⁻¹ • V.weight.map (fun x => R⁻¹ • (x - c)) ∧ V'.support = (fun x => c + R • x) ⁻¹' V.support ∧ (∀ x, V'.tangentProj x = V.tangentProj (c + R • x)) ∧ ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun x => R • H (c + R • x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
