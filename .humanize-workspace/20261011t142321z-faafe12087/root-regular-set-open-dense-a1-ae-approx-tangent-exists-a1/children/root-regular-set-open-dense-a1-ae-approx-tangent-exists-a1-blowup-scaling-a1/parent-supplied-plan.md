# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.blowup_scaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-blowup-scaling-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- Child key: `blowup_scaling`
- Declaration: `Submission.rsod_blowUpMap_measure_scaling`
- Exact Lean type: `∀ (n ℓ : ℕ) (x : Amb n ℓ) (r : ℝ), 0 < r → ∀ B : Set (Amb n ℓ), ENNReal.ofReal (r ^ n) * (μHE[n] : Measure (Amb n ℓ)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B) = (μHE[n] : Measure (Amb n ℓ)) B ∧ ((μHE[n] : Measure (Amb n ℓ)).restrict B).map (Poincare.SimonGMT.Chapter03.blowUpMap x r) = ENNReal.ofReal (r ^ n) • (μHE[n] : Measure (Amb n ℓ)).restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
