# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_height_estimate-a1.height_field_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-height-field-divergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_height_estimate-a1`
- Child key: `height_field_divergence`
- Declaration: `Submission.divM_height_test_field_eq`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ζ : Amb n ℓ → ℝ) (ξ x : Amb n ℓ) (P T : Submodule ℝ (Amb n ℓ)), DifferentiableAt ℝ ζ x → Module.finrank ℝ P = n → Module.finrank ℝ T = n → V.tangentProj x = P.starProjection → V.divM (fun y => ζ y ^ 2 • Tᗮ.starProjection (y - ξ)) x = ζ x ^ 2 * (hsNormSq (P.starProjection - T.starProjection) / 2) + 2 * ζ x * fderiv ℝ ζ x ((P.starProjection - T.starProjection) (Tᗮ.starProjection (x - ξ)))`

## Sibling prerequisites

- `root.tilt_excess_height_estimate-a1.projection_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
