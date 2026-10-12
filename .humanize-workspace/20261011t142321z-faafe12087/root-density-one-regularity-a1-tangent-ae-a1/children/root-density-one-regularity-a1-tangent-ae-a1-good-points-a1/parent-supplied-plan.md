# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.tangent_ae-a1.good_points-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-good-points-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.tangent_ae-a1`
- Child key: `good_points`
- Declaration: `Submission.tae_weightedApproxTangent_ae_on_piece`
- Exact Lean type: `∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (C N : Set (Amb n ℓ)) (T : Amb n ℓ → Submodule ℝ (Amb n ℓ)), 1 ≤ n → IsOpen U → IsCompact C → C ⊆ V.carrier → ContinuousOn V.mult C → MeasurableSet N → (μHE[n] : Measure (Amb n ℓ)) N < ⊤ → (∀ x ∈ N, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N x (T x)) → ∀ᵐ x ∂((μHE[n] : Measure (Amb n ℓ)).restrict (C ∩ N)), Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x (T x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
