# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-smoot-6b0404974b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1`
- Child key: `smooth_form_approx`
- Declaration: `Submission.regcomp_exists_smooth_unit_form_approx`
- Exact Lean type: `∀ (P n : ℕ) (ν : Measure (Euclid P)) (O K : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → IsOpen O → IsCompact K → K ⊆ O → AEStronglyMeasurable g ν → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → (∀ x, x ∉ K → g x = 0) → ∀ ε : ℝ, 0 < ε → ∃ h : DifferentialForm (Euclid P) n, IsTestForm h ∧ tsupport h ⊆ O ∧ (∀ z, covectorEuclideanNorm (h z) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (h x - g x)) ∂ν < ENNReal.ofReal ε`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.covector_eval_le-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
