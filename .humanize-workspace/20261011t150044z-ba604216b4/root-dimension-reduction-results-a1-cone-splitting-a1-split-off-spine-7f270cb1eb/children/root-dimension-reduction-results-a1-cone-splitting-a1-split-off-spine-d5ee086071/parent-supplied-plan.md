# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.product_box_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-d5ee086071/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child key: `product_box_measure`
- Declaration: `Submission.dimred_cs_sos_mt_product_box_measure`
- Exact Lean type: `∀ (P k : ℕ) (G : Submodule ℝ (Euclid P)) (ν σ : Measure (Euclid P)) (E : Set (Euclid P)), σ (Gᗮ : Set (Euclid P))ᶜ = 0 → MeasurableSet E → E ⊆ (G : Set (Euclid P)) → (∀ A : Set (Euclid P), MeasurableSet A → ν A = ∫⁻ t in E, σ ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → ∀ C B : Set (Euclid P), MeasurableSet C → MeasurableSet B → ν (G.starProjection ⁻¹' C ∩ Gᗮ.starProjection ⁻¹' B) = μHE[k] (E ∩ C) * σ B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
