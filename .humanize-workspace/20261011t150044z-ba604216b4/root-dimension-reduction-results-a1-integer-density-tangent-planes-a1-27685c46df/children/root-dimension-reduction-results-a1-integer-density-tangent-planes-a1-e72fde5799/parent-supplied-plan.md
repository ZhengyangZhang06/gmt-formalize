# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.alpha_beta-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-e72fde5799/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1`
- Child key: `alpha_beta`
- Declaration: `Submission.idtp_cse_fd_alpha_beta`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (R : IMRep (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s : ℝ) (H : ℝ × ℝ → ℝ), IsConeCurrent C → R.Represents C → 0 < s → s ≤ 1 / 4 → (∀ r : ℝ, 0 < r → ∀ᵐ x ∂R.measure, approxTangentPlane 2 R.carrier (r • x) = approxTangentPlane 2 R.carrier x) → (∀ b : ℝ × ℝ → ℝ, Measurable b → (∃ M : ℝ, ∀ p, |b p| ≤ M) → ∫ p : ℝ × ℝ, b p * H p = ∫ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, b (‖x‖, Real.arctan (inner ℝ x e / inner ℝ x a)) * (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2) ∂R.measure) → (∀ ψ l : ℝ → ℝ, ContDiff ℝ 1 ψ → ContDiff ℝ 1 l → tsupport ψ ⊆ Ioo (-s) s → tsupport l ⊆ Ioo (1 - s) (1 + s) → ∫ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) * l ‖x‖ * (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2) ∂R.measure = 0) → (∀ ψ l : ℝ → ℝ, ContDiff ℝ 1 ψ → ContDiff ℝ 1 l → tsupport ψ ⊆ Ioo (-s) s → tsupport l ⊆ Ioo (1 - s) (1 + s) → ∫ p : ℝ × ℝ, deriv ψ p.2 * l p.1 * H p = 0) ∧ (∀ (l ψ : ℝ → ℝ) (r : ℝ), ContDiff ℝ 1 l → ContDiff ℝ 1 ψ → tsupport l ⊆ Ioo (1 - s / 2) (1 + s / 2) → tsupport ψ ⊆ Ioo (-s) s → |r - 1| < s / 4 → ∫ p : ℝ × ℝ, l (p.1 / r) * ψ p.2 * H p = r ^ 2 * ∫ p : ℝ × ℝ, l p.1 * ψ p.2 * H p)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.flux_density-a1.cone_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
