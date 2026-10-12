# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.radial_homogeneity-a1.euler_dilation_c1-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-radial-homogeneity-a1-euler-dilation-c1-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.radial_homogeneity-a1`
- Child key: `euler_dilation_c1`
- Declaration: `Submission.varifold_tangents_rh_scaling_of_euler_identity`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)), IsFiniteMeasureOnCompacts μ → (∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∫ y, ((n : ℝ) * g y + fderiv ℝ g y y) ∂μ = 0) → ∀ g : Euclidean N → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∀ s : ℝ, 0 < s → ∫ y, g (s⁻¹ • y) ∂μ = s ^ n * ∫ y, g y ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
