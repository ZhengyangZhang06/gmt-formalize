# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.mass_eq_weight-a1.weight_le_mass-a1.integral_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-weight-le-mass-a1-integra-a67a38d715/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.mass_eq_weight-a1.weight_le_mass-a1`
- Child key: `integral_estimate`
- Declaration: `Submission.rsd_mw_wlm_sub_lt_integral`
- Exact Lean type: `∀ (P n : ℕ) (ν : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β ω : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsFiniteMeasure ν → AEStronglyMeasurable ξ ν → Continuous ω → (∀ x, covectorEuclideanNorm (ω x) ≤ 1) → (∀ᵐ x ∂ν, (∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) ∧ ξ x (β x) = 1) → ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν < ENNReal.ofReal ε → (ν univ).toReal - ε < ∫ x, ξ x (ω x) ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
