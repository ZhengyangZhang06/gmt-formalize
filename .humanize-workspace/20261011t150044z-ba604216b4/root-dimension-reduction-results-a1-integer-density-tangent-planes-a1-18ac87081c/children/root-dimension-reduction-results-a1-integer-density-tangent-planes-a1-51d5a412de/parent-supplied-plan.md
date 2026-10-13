# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-51d5a412de/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1`
- Child key: `edge_tangent_plane`
- Declaration: `Submission.idtp_cse_edge_tangent_plane`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (δ : ℝ) (k : ℕ), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < δ → 1 ≤ k → a ∈ C.support → (∀ t φ : ℝ, 0 < t → 0 < φ → φ < δ → HasMassDensity C (t • (Real.cos φ • a + Real.sin φ • e)) k ∧ ∃ r : ℝ, 0 < r ∧ C.support ∩ ball (t • (Real.cos φ • a + Real.sin φ • e)) r ⊆ (Q : Set (Euclid P))) → ∃ m : ℕ, 1 ≤ m ∧ HasMassDensity C a m ∧ (∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C' : GeometricCurrentOn (univ : Set (Euclid P)) 2) (c : ℤ), StrictMono φ ∧ c.natAbs = m ∧ ConvergesWeakly (fun j => blowUp C a (lams (φ j)) (hlams (φ j)).ne') C' ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) 2, C' ω = (c : ℝ) * ∫ x in (Q : Set (Euclid P)), (ω : DifferentialForm (Euclid P) 2) x ![a, e] ∂μHE[2]) ∧ ∀ R : IMRep (univ : Set (Euclid P)) 2, R.Represents C → ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams (φ j))⁻¹ ^ 2 * ∫ x, g (dilation a (lams (φ j)) x) ∂R.measure) atTop (𝓝 ((m : ℝ) * ∫ x in (Q : Set (Euclid P)), g x ∂μHE[2]))) ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 4 ∧ (∀ s' : ℝ, 0 < s' → s' ≤ s₀ → ∀ x ∈ C.support, 0 < inner ℝ x a → |‖x‖ - 1| < s' → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' → ‖x - Q.starProjection x‖ ≤ 2 * s₀ * ‖x‖ → ‖x - Q.starProjection x‖ < s' / 4 * ‖x‖ ∧ dist x a < 3 * s')`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.mass_lower_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
