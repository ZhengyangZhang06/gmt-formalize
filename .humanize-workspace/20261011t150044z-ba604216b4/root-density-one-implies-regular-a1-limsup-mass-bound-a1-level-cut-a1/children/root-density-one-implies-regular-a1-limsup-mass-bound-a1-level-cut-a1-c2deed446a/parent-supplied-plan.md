# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.level_cut-a1.good_radius-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-level-cut-a1-c2deed446a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.level_cut-a1`
- Child key: `good_radius`
- Declaration: `Submission.dor_lmb_glc_good_radius`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (ρ ρ' : ℝ) (g : ℝ → ℝ≥0∞) (I : ℝ≥0∞) (p : ℝ → Prop), ρ < ρ' → μ (closedBall y ρ') ≠ ∞ → AEMeasurable g → ∫⁻ t, g t ≤ I → (∀ᵐ t, p t) → ∃ t : ℝ, ρ < t ∧ t < ρ' ∧ p t ∧ μ (sphere y t) = 0 ∧ g t ≤ ENNReal.ofReal (2 / (ρ' - ρ)) * I`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
