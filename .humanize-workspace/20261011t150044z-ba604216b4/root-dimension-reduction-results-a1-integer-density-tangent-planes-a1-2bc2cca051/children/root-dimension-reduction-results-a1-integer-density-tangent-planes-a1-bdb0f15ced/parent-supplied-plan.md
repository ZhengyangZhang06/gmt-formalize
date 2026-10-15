# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1.fibre_pointwise-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-bdb0f15ced/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1`
- Child key: `fibre_pointwise`
- Declaration: `Submission.idtp_cse_fc_fibre_pointwise`
- Exact Lean type: `∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s : ℝ) (m k : ℕ) (p : ℝ × ℝ), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < s → s ≤ 1 / 4 → |p.1 - 1| < s → |p.2| < s → ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞) * ENNReal.ofReal ‖(approxTangentPlane 2 R.carrier (x : Euclid P)).starProjection (inner ℝ (x : Euclid P) a • e - inner ℝ (x : Euclid P) e • a)‖ = ENNReal.ofReal ((m : ℝ) * p.1) → (m : ℝ≥0∞) ≤ ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞) ∧ ((p.1 • (Real.cos p.2 • a + Real.sin p.2 • e)) ∈ R.carrier → R.mult (p.1 • (Real.cos p.2 • a + Real.sin p.2 • e)) = k → approxTangentPlane 2 R.carrier (p.1 • (Real.cos p.2 • a + Real.sin p.2 • e)) = Q → k ≤ m ∧ (k < m → (m : ℝ≥0∞) + 1 ≤ ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞)))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1.planar_geometry-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_count-a1.count_arith-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
