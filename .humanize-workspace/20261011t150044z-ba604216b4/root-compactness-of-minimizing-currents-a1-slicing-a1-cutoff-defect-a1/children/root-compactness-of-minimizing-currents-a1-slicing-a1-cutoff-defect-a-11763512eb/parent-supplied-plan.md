# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.defect_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-cutoff-defect-a-11763512eb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1`
- Child key: `defect_identity`
- Declaration: `Submission.cmcs_cd_defect_identity`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = -∫ x, ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x))) ∂μ`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.leibniz-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.smul_test_form-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
