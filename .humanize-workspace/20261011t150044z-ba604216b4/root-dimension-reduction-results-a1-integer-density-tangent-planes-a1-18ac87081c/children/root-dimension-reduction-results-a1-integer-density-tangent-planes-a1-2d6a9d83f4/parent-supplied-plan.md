# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2d6a9d83f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1`
- Child key: `fibre_area`
- Declaration: `Submission.idtp_cse_fibre_area_identities`
- Exact Lean type: `∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s : ℝ), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → (∀ᵐ x ∂R.measure, (approxTangentPlane 2 R.carrier x).starProjection x = x) → AEMeasurable (fun p : ℝ × ℝ => ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞) * ENNReal.ofReal ‖(approxTangentPlane 2 R.carrier (x : Euclid P)).starProjection (inner ℝ (x : Euclid P) a • e - inner ℝ (x : Euclid P) e • a)‖) volume ∧ AEMeasurable (fun p : ℝ × ℝ => ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞)) volume ∧ ∀ b : ℝ × ℝ → ℝ≥0∞, Measurable b → (∫⁻ p : ℝ × ℝ, b p * ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞) * ENNReal.ofReal ‖(approxTangentPlane 2 R.carrier (x : Euclid P)).starProjection (inner ℝ (x : Euclid P) a • e - inner ℝ (x : Euclid P) e • a)‖ = ∫⁻ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, b (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a)) * ENNReal.ofReal (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2) ∂R.measure) ∧ (∫⁻ p : ℝ × ℝ, b p * ∑' x : ↥(R.carrier ∩ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ (fun x : Euclid P => (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a))) ⁻¹' {p}), (R.mult x : ℝ≥0∞) = ∫⁻ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, b (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a)) * ENNReal.ofReal (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ / ‖Q.starProjection x‖ ^ 2) ∂R.measure)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
