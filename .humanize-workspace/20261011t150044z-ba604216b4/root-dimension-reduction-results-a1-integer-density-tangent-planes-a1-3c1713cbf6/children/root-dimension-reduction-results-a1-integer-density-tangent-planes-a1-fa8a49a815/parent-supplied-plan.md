# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.glue_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-fa8a49a815/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1`
- Child key: `glue_pieces`
- Declaration: `Submission.idtp_caf_glue_pieces`
- Exact Lean type: `∀ (P n : ℕ) (ι : Type) [Countable ι] (S : Set (Euclid P)) (pieces : ι → Set (Euclid P)) (F : Euclid P → Euclid n) (φ h : Euclid P → ℝ≥0∞), (∀ k, MeasurableSet (pieces k)) → (∀ k, pieces k ⊆ S) → Pairwise (fun k k' => Disjoint (pieces k) (pieces k')) → μHE[n] (S \ ⋃ k, pieces k) = 0 → volume (F '' (S \ ⋃ k, pieces k)) = 0 → (∀ k, AEMeasurable (fun y : Euclid n => ∑' x : ↥(pieces k ∩ F ⁻¹' {y}), h x) volume ∧ ∫⁻ y, (∑' x : ↥(pieces k ∩ F ⁻¹' {y}), h x) ∂volume = ∫⁻ x in pieces k, φ x * h x ∂μHE[n]) → AEMeasurable (fun y : Euclid n => ∑' x : ↥(S ∩ F ⁻¹' {y}), h x) volume ∧ ∫⁻ y, (∑' x : ↥(S ∩ F ⁻¹' {y}), h x) ∂volume = ∫⁻ x in S, φ x * h x ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
