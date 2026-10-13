# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.density_one_flat_covers-a1.graph_piece_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-density-one-flat-covers-a1-graph-piece-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.density_one_flat_covers-a1`
- Child key: `graph_piece_bounds`
- Declaration: `Submission.frt_graph_piece_density_bounds`
- Exact Lean type: `∀ (N n : ℕ) (A Γ : Set (Euclidean N)) (P : Grassmannian N n) (L : ℝ), μHE[n] A ≠ ∞ → NullMeasurableSet A μHE[n] → 0 ≤ L → IsClosed Γ → (∀ y ∈ Γ, ∀ z ∈ Γ, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → ∀ᵐ x ∂((μHE[n] : Measure (Euclidean N)).restrict A).restrict Γ, (ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n)⁻¹ ≤ liminf (densityRatio n ((μHE[n] : Measure (Euclidean N)).restrict A) x) (𝓝[>] 0) ∧ limsup (densityRatio n ((μHE[n] : Measure (Euclidean N)).restrict A) x) (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n`

## Sibling prerequisites

- `root.first_rectifiability-a1.density_one_flat_covers-a1.plane_density-a1`
- `root.first_rectifiability-a1.density_one_flat_covers-a1.graph_projection_compare-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
