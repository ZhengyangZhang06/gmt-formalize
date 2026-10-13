# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1.euler_identity_dilates-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-radial-homogeneity-a1-euler-dilation-c1-a1-5e6e076fe4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1`
- Child key: `euler_identity_dilates`
- Declaration: `Submission.varifold_tangents_rh_edc_euler_dilate`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)), IsFiniteMeasureOnCompacts μ → (∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∫ y, ((n : ℝ) * g y + fderiv ℝ g y y) ∂μ = 0) → ∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∀ t : ℝ, 0 < t → (n : ℝ) * (∫ y, g (t⁻¹ • y) ∂μ) + ∫ y, fderiv ℝ g (t⁻¹ • y) (t⁻¹ • y) ∂μ = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
