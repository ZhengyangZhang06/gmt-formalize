# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.smooth_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-smooth-cutoff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1`
- Child key: `smooth_cutoff`
- Declaration: `Submission.rsd_mw_tfa_smooth_cutoff`
- Exact Lean type: `∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → ∀ δ : ℝ, 0 < δ → ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ν {x | χ x ≠ 1} < ENNReal.ofReal δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
