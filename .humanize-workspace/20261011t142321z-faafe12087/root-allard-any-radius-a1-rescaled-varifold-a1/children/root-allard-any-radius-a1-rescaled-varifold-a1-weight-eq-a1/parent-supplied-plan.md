# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.rescaled_varifold-a1.weight_eq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-rescaled-varifold-a1-weight-eq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.rescaled_varifold-a1`
- Child key: `weight_eq`
- Declaration: `Submission.any_radius_rv_weight_eq`
- Exact Lean type: `∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (W : RectifiableVarifold n ℓ U') (c : Amb n ℓ) (R : ℝ), 0 < R → W.carrier = (fun x => c + R • x) ⁻¹' V.carrier → (∀ x, W.mult x = V.mult (c + R • x)) → W.weight = (ENNReal.ofReal (R ^ n))⁻¹ • V.weight.map (fun x => R⁻¹ • (x - c))`

## Sibling prerequisites

- `root.allard_any_radius-a1.rescaled_varifold-a1.map_hausdorff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
