# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1.smooth_support_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-smoot-18fb62e6b6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1`
- Child key: `smooth_support_approx`
- Declaration: `Submission.regcomp_exists_smooth_unit_form_support_approx`
- Exact Lean type: `∀ (P n : ℕ) (f : Euclid P → Covector (Euclid P) n), Continuous f → HasCompactSupport f → (∀ z, covectorEuclideanNorm (f z) ≤ 1) → ∀ κ : ℝ, 0 < κ → ∃ h : DifferentialForm (Euclid P) n, IsTestForm h ∧ support h ⊆ support f ∧ (∀ z, covectorEuclideanNorm (h z) ≤ 1) ∧ ∀ z, covectorEuclideanNorm (h z - f z) ≤ κ`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1.coeff_norm_toolkit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
