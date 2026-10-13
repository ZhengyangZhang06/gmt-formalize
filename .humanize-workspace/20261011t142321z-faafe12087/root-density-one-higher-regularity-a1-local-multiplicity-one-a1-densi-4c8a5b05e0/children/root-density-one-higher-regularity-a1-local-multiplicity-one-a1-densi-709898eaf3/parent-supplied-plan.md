# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_eq_mult_ae-a1.weight_restrict_withdensity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-densi-709898eaf3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1.density_eq_mult_ae-a1`
- Child key: `weight_restrict_withdensity`
- Declaration: `Submission.dohr_lmo_dema_weight_restrict_withDensity`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (O : Set (Amb n ℓ)), MeasurableSet O → O ⊆ U → V.weight.restrict O = ((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O)).withDensity (fun x => ENNReal.ofReal (V.carrier.indicator V.mult x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
