# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1.perturbation_injective-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-ba2245ebec/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.first_variation-a1`
- Child key: `perturbation_injective`
- Declaration: `Submission.codim1_hcp_fv_perturbation_injective`
- Exact Lean type: `∀ (P : ℕ) (Z : Euclid P → Euclid P), ContDiff ℝ 1 Z → HasCompactSupport Z → ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, |t| < c → Injective (fun x => x + t • Z x) ∧ ∀ x, Injective (fderiv ℝ (fun x => x + t • Z x) x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
