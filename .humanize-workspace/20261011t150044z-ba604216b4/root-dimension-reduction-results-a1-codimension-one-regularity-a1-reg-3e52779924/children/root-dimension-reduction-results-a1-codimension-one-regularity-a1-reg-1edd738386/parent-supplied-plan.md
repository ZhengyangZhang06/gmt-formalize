# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.lintegral_split-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1edd738386/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1`
- Child key: `lintegral_split`
- Declaration: `Submission.codim1_lura_lintegral_image_eq_tsum_pieces`
- Exact Lean type: `∀ (m d P : ℕ) (M : Set (Euclid d)) (A : ℕ → Set (Euclid d)) (G : Euclid d → Euclid P), ContinuousOn G M → InjOn G M → (∀ i, MeasurableSet (A i)) → (∀ i, A i ⊆ M) → Pairwise (fun i j => Disjoint (A i) (A j)) → μHE[m] (G '' (M \ ⋃ i, A i)) = 0 → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ w in G '' M, g w ∂μHE[m] = ∑' i, ∫⁻ w in G '' A i, g w ∂μHE[m]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
