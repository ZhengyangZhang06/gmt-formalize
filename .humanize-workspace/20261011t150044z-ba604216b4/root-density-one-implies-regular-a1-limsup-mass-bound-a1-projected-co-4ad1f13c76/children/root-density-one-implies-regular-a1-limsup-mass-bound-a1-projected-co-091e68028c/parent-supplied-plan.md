# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1.pullback_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-co-091e68028c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1`
- Child key: `pullback_field`
- Declaration: `Submission.dor_lmb_pc_cm_pullback_field_bounded`
- Exact Lean type: `∀ (P n : ℕ) (G O : Set (Euclid P)) (f : Euclid P → Euclid P) (ω : DifferentialForm (Euclid P) n) (Λ W : ℝ), IsOpen G → IsOpen O → G ⊆ O → ContDiffOn ℝ 1 f O → Continuous ω → 0 ≤ Λ → (∀ x ∈ G, ‖fderiv ℝ f x‖ ≤ Λ) → (∀ z, ‖ω z‖ ≤ W) → (∀ μ : Measure (Euclid P), AEStronglyMeasurable (G.indicator fun y => (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)) μ) ∧ ∀ x, ‖G.indicator (fun y => (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)) x‖ ≤ W * Λ ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
