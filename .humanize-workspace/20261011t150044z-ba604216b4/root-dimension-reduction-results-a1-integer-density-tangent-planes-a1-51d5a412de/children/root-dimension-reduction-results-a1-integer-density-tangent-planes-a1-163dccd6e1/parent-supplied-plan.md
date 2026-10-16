# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.blowup_vague_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-163dccd6e1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1`
- Child key: `blowup_vague_limit`
- Declaration: `Submission.idtp_cse_etp_blowup_vague_limit`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (a : Euclid P) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j) (C' : GeometricCurrentOn (univ : Set (Euclid P)) n) (τ : Fin n → Euclid P) (c : ℤ), Orthonormal ℝ τ → c ≠ 0 → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, C' ω = (c : ℝ) * ∫ x in (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) → MassMeasuresConverge (fun j => blowUp C a (lams j) (hlams j).ne') C' → ∀ R : IMRep (univ : Set (Euclid P)) n, R.Represents C → ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams j)⁻¹ ^ n * ∫ x, g (dilation a (lams j) x) ∂R.measure) atTop (𝓝 ((c.natAbs : ℝ) * ∫ x in (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x ∂μHE[n]))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.plane_imrep-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
