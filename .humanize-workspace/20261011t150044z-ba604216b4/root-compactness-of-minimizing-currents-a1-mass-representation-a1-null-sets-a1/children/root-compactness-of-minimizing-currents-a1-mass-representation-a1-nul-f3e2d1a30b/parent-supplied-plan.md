# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1.localize_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-nul-f3e2d1a30b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1`
- Child key: `localize_null`
- Declaration: `Submission.cmr_ae_zero_of_div_bounds`
- Exact Lean type: `∀ (P n : ℕ) (W : Set (Euclid P)) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (q : Euclid P → Euclid n) (N : Set (Euclid n)) (c : ℝ), IsOpen W → μ W < ∞ → AEStronglyMeasurable f μ → (∀ x, |f x| ≤ c) → Measurable q → MeasurableSet N → (∀ (ν : Measure (Euclid P)) (h : Euclid P → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∫ x in q ⁻¹' N, h x ∂ν = 0) → (∀ b : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ W → ∃ Λ : ℝ, ∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, b x * f x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂(μ.restrict W)| ≤ Λ) → ∀ᵐ x ∂μ, x ∈ W → q x ∈ N → f x = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
