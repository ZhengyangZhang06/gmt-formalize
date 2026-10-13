# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1.dilation_integral_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-radial-homogeneity-a1-euler-dilation-c1-a1-669b0db0b7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1`
- Child key: `dilation_integral_deriv`
- Declaration: `Submission.varifold_tangents_rh_edc_hasDerivAt_dilate_integral`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)), IsFiniteMeasureOnCompacts μ → ∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∀ t : ℝ, 0 < t → HasDerivAt (fun r : ℝ => ∫ y, g (r⁻¹ • y) ∂μ) (-(t⁻¹ * ∫ y, fderiv ℝ g (t⁻¹ • y) (t⁻¹ • y) ∂μ)) t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
