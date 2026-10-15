# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1.truncation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-truncated-compa-ecfcbb20bf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1`
- Child key: `truncation`
- Declaration: `Submission.dimred_mbl_tc_truncate_at_good_radius`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (S A : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)) (ρ s : ℝ), IsOpen U → R.Represents S → (∀ β : TestFormOn U m, tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 s → S.boundary β = 0) → 0 < ρ → ρ < s → ball (0 : Euclid P) s ⊆ U → (∀ ω : TestFormOn U (m + 1), A ω = ∫ x in ball (0 : Euclid P) ρ, R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂R.measure) → A.boundary.massOn (ball 0 s) ≠ ∞ → ∃ (Ŝ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R' : IMRep (univ : Set (Euclid P)) (m + 1)), R'.Represents Ŝ ∧ R'.measure = R.measure.restrict (ball 0 ρ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 ρ → Ŝ ω = currentEval S (ω : DifferentialForm (Euclid P) (m + 1))) ∧ (∀ β : TestFormOn (univ : Set (Euclid P)) m, tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 ρ → Ŝ.boundary β = 0) ∧ Ŝ.boundary.massOn univ ≤ A.boundary.massOn (ball 0 s)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.eval_mass_bound-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.imrep_restriction-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
