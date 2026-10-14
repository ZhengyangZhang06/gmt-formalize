# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1.mass_le-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-e002264f16/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1`
- Child key: `mass_le`
- Declaration: `Submission.cbr_ci_pw_proj_mass_le`
- Exact Lean type: `∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l) (Y : GeometricCurrentOn U l), IsOpen U → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → (∀ ω : TestFormOn U l, Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ) → Y.massOn U ≤ μ (F ∩ pL ⁻¹' U)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
