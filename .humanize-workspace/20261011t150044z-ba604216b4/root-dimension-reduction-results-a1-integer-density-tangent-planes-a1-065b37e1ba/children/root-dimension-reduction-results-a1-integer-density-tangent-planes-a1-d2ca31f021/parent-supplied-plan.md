# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_area_formula-a1.fiber_sum_ae_congr-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d2ca31f021/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_area_formula-a1`
- Child key: `fiber_sum_ae_congr`
- Declaration: `Submission.idtp_caf_paf_fiberSum_ae_congr`
- Exact Lean type: `∀ (P n : ℕ) (S V : Set (Euclid P)) (F G : Euclid P → Euclid n) (LG : NNReal) (h h' : Euclid P → ℝ≥0∞), S ⊆ V → LipschitzWith LG G → EqOn F G V → h =ᵐ[μHE[n].restrict S] h' → (fun y : Euclid n => ∑' x : ↥(S ∩ F ⁻¹' {y}), h x) =ᵐ[volume] (fun y : Euclid n => ∑' x : ↥(S ∩ F ⁻¹' {y}), h' x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
