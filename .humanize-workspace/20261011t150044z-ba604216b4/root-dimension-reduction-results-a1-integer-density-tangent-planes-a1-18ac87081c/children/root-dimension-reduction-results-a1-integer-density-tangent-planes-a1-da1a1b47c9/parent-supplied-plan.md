# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.box_mass_limits-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-da1a1b47c9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1`
- Child key: `box_mass_limits`
- Declaration: `Submission.idtp_cse_edge_box_mass_limits`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (δ : ℝ) (k : ℕ), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < δ → 1 ≤ k → a ∈ C.support → (∀ t φ : ℝ, 0 < t → 0 < φ → φ < δ → HasMassDensity C (t • (Real.cos φ • a + Real.sin φ • e)) k ∧ ∃ r : ℝ, 0 < r ∧ C.support ∩ ball (t • (Real.cos φ • a + Real.sin φ • e)) r ⊆ (Q : Set (Euclid P))) → ∀ (R : IMRep (univ : Set (Euclid P)) 2) (m : ℕ) (s : ℝ), R.Represents C → HasMassDensity C a m → 0 < s → s ≤ 1 / 4 → (∀ s' : ℝ, 0 < s' → s' ≤ s → ∀ x ∈ C.support, 0 < inner ℝ x a → |‖x‖ - 1| < s' → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' → ‖x - Q.starProjection x‖ ≤ 2 * s * ‖x‖ → ‖x - Q.starProjection x‖ < s' / 4 * ‖x‖ ∧ dist x a < 3 * s') → Tendsto (fun s' : ℝ => R.measure {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} / ENNReal.ofReal (s' ^ 2)) (𝓝[>] 0) (𝓝 (4 * (m : ℝ≥0∞))) ∧ Tendsto (fun s' : ℝ => (∫⁻ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, ENNReal.ofReal (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2) ∂R.measure) / ENNReal.ofReal (s' ^ 2)) (𝓝[>] 0) (𝓝 (4 * (m : ℝ≥0∞)))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.stationary_radial-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
