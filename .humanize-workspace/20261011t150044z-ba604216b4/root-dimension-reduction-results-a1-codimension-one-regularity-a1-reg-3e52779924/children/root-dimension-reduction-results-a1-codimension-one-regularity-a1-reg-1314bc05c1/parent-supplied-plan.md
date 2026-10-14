# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.borel_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1314bc05c1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1`
- Child key: `borel_glue`
- Declaration: `Submission.codim1_lura_glue_measurable_on_pieces`
- Exact Lean type: `∀ (m d : ℕ) (F : ℕ → Euclid m → Euclid d) (B : ℕ → Set (Euclid m)) (h : ℕ → Euclid m → ℝ), (∀ i, Continuous (F i)) → (∀ i, MeasurableSet (B i)) → (∀ i, InjOn (F i) (B i)) → Pairwise (fun i j => Disjoint (F i '' B i) (F j '' B j)) → (∀ i, Measurable (h i)) → (∀ i a, 0 ≤ h i a) → ∃ J : Euclid d → ℝ, Measurable J ∧ (∀ v, 0 ≤ J v) ∧ ∀ i, ∀ b ∈ B i, J (F i b) = h i b`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
