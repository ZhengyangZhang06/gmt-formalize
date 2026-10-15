# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.sector_points-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-64496f9e64/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1`
- Child key: `sector_points`
- Declaration: `Submission.idtp_cse_sector_carrier_points`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (δ : ℝ) (k : ℕ) (R : IMRep (univ : Set (Euclid P)) 2), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < δ → 1 ≤ k → (∀ t φ : ℝ, 0 < t → 0 < φ → φ < δ → HasMassDensity C (t • (Real.cos φ • a + Real.sin φ • e)) k ∧ ∃ r : ℝ, 0 < r ∧ C.support ∩ ball (t • (Real.cos φ • a + Real.sin φ • e)) r ⊆ (Q : Set (Euclid P))) → R.Represents C → ∀ᵐ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 → p.2 < δ → p.2 < 1 → (p.1 • (Real.cos p.2 • a + Real.sin p.2 • e)) ∈ R.carrier ∧ R.mult (p.1 • (Real.cos p.2 • a + Real.sin p.2 • e)) = k ∧ approxTangentPlane 2 R.carrier (p.1 • (Real.cos p.2 • a + Real.sin p.2 • e)) = Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
