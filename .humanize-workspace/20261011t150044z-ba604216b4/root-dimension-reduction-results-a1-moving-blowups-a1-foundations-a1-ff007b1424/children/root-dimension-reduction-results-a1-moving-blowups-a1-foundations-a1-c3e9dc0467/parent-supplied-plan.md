# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1.uniform_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-foundations-a1-c3e9dc0467/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.testform_extension-a1`
- Child key: `uniform_approx`
- Declaration: `Submission.dimred_mbl_fnd_tfe_uniform_testForm_approx`
- Exact Lean type: `∀ (P n d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (V : Set (Euclid P)) (G : Euclid P → Covector (Euclid P) n) (ε : ℝ), (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → IsOpen V → Continuous G → HasCompactSupport G → tsupport G ⊆ V → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ ∀ x, covectorEuclideanNorm (ω x - G x) ≤ ε`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1.mollify_unit_field-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
