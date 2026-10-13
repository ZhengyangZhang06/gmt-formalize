# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1.continuous_l1_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-smoot-b142463c2e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1`
- Child key: `continuous_l1_approx`
- Declaration: `Submission.regcomp_exists_continuous_unit_form_approx`
- Exact Lean type: `∀ (P n : ℕ) (ν : Measure (Euclid P)) (O K : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → IsOpen O → IsCompact K → K ⊆ O → Integrable g ν → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → (∀ x, x ∉ K → g x = 0) → ∀ ε : ℝ, 0 < ε → ∃ f : Euclid P → Covector (Euclid P) n, Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧ (∀ z, covectorEuclideanNorm (f z) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (f x - g x)) ∂ν ≤ ENNReal.ofReal ε`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1.coeff_norm_toolkit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
