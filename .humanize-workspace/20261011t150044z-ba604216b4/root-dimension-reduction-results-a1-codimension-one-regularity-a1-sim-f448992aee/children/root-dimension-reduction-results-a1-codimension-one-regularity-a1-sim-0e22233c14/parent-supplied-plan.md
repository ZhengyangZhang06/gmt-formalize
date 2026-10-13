# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.perturbation_diffeo-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-0e22233c14/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1`
- Child key: `perturbation_diffeo`
- Declaration: `Submission.codim1_ac_perturbation_diffeo`
- Exact Lean type: `∀ (P : ℕ) (Z : Euclid P → Euclid P), ContDiff ℝ 1 Z → HasCompactSupport Z → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ → Bijective (fun x => x + t • Z x) ∧ (∀ x, Injective (fderiv ℝ (fun x => x + t • Z x) x)) ∧ ∃ Λ : NNReal, LipschitzWith Λ (fun x => x + t • Z x) ∧ AntilipschitzWith Λ (fun x => x + t • Z x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
