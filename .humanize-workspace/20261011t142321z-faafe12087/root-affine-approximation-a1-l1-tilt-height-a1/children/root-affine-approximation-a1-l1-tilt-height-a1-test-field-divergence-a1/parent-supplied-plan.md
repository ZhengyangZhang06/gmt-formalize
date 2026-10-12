# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.l1_tilt_height-a1.test_field_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-l1-tilt-height-a1-test-field-divergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.l1_tilt_height-a1`
- Child key: `test_field_divergence`
- Declaration: `Submission.aal_l1th_test_field_divergence`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ζ : Amb n ℓ → ℝ) (z x : Amb n ℓ) (P T : Submodule ℝ (Amb n ℓ)), DifferentiableAt ℝ ζ x → Module.finrank ℝ P = n → Module.finrank ℝ T = n → V.tangentProj x = P.starProjection → V.divM (fun y => ζ y ^ 2 • Tᗮ.starProjection (y - z)) x = ζ x ^ 2 * (hsNormSq (V.tangentProj x - T.starProjection) / 2) + 2 * ζ x * fderiv ℝ ζ x ((V.tangentProj x - T.starProjection) (Tᗮ.starProjection (x - z)))`

## Sibling prerequisites

- `root.affine_approximation-a1.l1_tilt_height-a1.projection_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
