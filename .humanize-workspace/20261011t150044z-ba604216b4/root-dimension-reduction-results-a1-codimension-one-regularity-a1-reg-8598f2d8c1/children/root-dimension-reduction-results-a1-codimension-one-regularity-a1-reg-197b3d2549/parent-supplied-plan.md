# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.orthogonal_fubini-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-197b3d2549/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child key: `orthogonal_fubini`
- Declaration: `Submission.codim1_rdo_dg_tma_orthogonal_fubini`
- Exact Lean type: `∀ (m : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1)) (v : Euclid (m + 1)), ‖v‖ = 1 → (∀ x, inner ℝ (ι x) v = 0) → MeasurePreserving (fun p : Euclid m × ℝ => ι p.1 + p.2 • v) volume volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
