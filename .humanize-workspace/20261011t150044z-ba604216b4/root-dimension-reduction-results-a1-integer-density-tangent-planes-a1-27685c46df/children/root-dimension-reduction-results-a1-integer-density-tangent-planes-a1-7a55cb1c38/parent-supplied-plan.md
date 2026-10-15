# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.fibre_signed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7a55cb1c38/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1`
- Child key: `fibre_signed`
- Declaration: `Submission.idtp_cse_fd_fibre_signed_identity`
- Exact Lean type: `∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s : ℝ) (H : ℝ × ℝ → ℝ≥0∞), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → AEMeasurable H volume → (∀ b : ℝ × ℝ → ℝ≥0∞, Measurable b → ∫⁻ p : ℝ × ℝ, b p * H p = ∫⁻ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, b (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a)) * ENNReal.ofReal (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2) ∂R.measure) → (∀ᵐ p : ℝ × ℝ, H p ≠ ∞) ∧ Integrable (fun p : ℝ × ℝ => (H p).toReal) ∧ (∀ b : ℝ × ℝ → ℝ, Measurable b → (∃ M : ℝ, ∀ p, |b p| ≤ M) → ∫ p : ℝ × ℝ, b p * (H p).toReal = ∫ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, b (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a)) * (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2) ∂R.measure) ∧ ∀ s' : ℝ, s' ≤ s → ∫⁻ p in Ioo (1 - s') (1 + s') ×ˢ Ioo (-s') s', H p = ∫⁻ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, ENNReal.ofReal (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2) ∂R.measure`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.tangent_projection_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
