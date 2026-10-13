# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.pushforward_rep-a1.normal_field_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-716bded54d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.pushforward_rep-a1`
- Child key: `normal_field_measurable`
- Declaration: `Submission.codim1_pfr_normal_multivector_measurable`
- Exact Lean type: `∀ (P n : ℕ) (G : Euclid (n + 1) → Euclid P) (ν : Euclid (n + 1) → Euclid (n + 1)), Measurable ν → ∃ ξ : Euclid (n + 1) → MultiVector P n, StronglyMeasurable ξ ∧ ∀ (v : Euclid (n + 1)) (α : Covector (Euclid P) n), ξ v α = -∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * α (fun k => fderiv ℝ G v (EuclideanSpace.single (j.succAbove k) (1 : ℝ))) * inner ℝ (EuclideanSpace.single j (1 : ℝ)) (ν v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
