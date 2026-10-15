# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.edge_direction_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7839170b61/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child key: `edge_direction_support`
- Declaration: `Submission.idtp_cse_etp_edge_direction_support`
- Exact Lean type: `∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (a e : Euclid P) (δ : ℝ) (k : ℕ), IsIntegerMultiplicity C → 0 < δ → 1 ≤ k → (∀ t φ : ℝ, 0 < t → 0 < φ → φ < δ → HasMassDensity C (t • (Real.cos φ • a + Real.sin φ • e)) k) → ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, 0 < l → l < l₀ → a + l • e ∈ C.support`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
