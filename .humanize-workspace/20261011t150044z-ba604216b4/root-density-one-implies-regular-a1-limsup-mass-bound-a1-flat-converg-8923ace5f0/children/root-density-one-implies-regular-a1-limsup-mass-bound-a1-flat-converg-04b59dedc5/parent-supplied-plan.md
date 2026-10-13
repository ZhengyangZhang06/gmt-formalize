# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.localize-a1.good_level-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-04b59dedc5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.localize-a1`
- Child key: `good_level`
- Declaration: `Submission.dor_lmb_fcl_good_level`
- Exact Lean type: `∀ (ν : ℕ → Measure ℝ) (F : ℕ → ℝ → ℝ≥0∞) (Good : ℕ → ℝ → Prop) (a b : ℝ) (Λ : ℝ≥0∞), a < b → Λ ≠ ∞ → (∀ j, ν j (Icc a b) ≤ Λ) → (∀ j, AEMeasurable (F j)) → (∀ j, ∫⁻ t, F j t ≤ Λ) → (∀ j, ∀ᵐ t, Good j t) → ∃ s ∈ Ioo a b, ∃ (φ : ℕ → ℕ) (C : ℝ≥0∞), StrictMono φ ∧ C ≠ ∞ ∧ (∀ j, Good j s) ∧ (∀ j, F (φ j) s ≤ C) ∧ ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, ν (φ j) (Icc (s - δ) s) ≤ ε`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.helly_no_concentration-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
