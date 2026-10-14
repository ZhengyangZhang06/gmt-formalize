# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.c1_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-c93e40078c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1`
- Child key: `c1_image`
- Declaration: `Submission.codim1_lura_c1_image_lipschitz_null_rectifiable`
- Exact Lean type: `∀ (m d P : ℕ) (D : Set (Euclid d)) (G : Euclid d → Euclid P), IsOpen D → ContDiffOn ℝ 1 G D → (∀ K : Set (Euclid d), IsCompact K → K ⊆ D → ∃ L : NNReal, LipschitzOnWith L G K) ∧ (∀ S : Set (Euclid d), S ⊆ D → μHE[m] S = 0 → μHE[m] (G '' S) = 0) ∧ ∀ S : Set (Euclid d), S ⊆ D → CountablyRectifiable m S → CountablyRectifiable m (G '' S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
