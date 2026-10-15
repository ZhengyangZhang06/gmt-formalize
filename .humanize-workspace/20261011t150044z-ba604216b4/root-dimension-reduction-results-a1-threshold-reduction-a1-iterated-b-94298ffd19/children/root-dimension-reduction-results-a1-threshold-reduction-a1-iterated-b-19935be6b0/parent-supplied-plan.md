# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1.countable_tests-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-iterated-b-19935be6b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1`
- Child key: `countable_tests`
- Declaration: `Submission.dimred_tr_ibl_countable_tests`
- Exact Lean type: `∀ (P n : ℕ), ∃ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, ∀ (Vs : ℕ → Set (Euclid P)) (As : (k : ℕ) → GeometricCurrentOn (Vs k) n) (A : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ R : ℕ, ∃ (k₀ : ℕ) (Γ : ℝ≥0∞), Γ ≠ ∞ ∧ A.massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ ∧ ∀ k, k₀ ≤ k → ball (0 : Euclid P) ((R : ℝ) + 1) ⊆ Vs k ∧ (As k).massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ) → (∀ m, Tendsto (fun k => currentEval (As k) ((ωs m : TestFormOn (univ : Set (Euclid P)) n) : DifferentialForm (Euclid P) n)) atTop (𝓝 (A (ωs m)))) → ConvergesWeakly As A`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1`
- `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.norm_props-a1`
- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.eval_mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
