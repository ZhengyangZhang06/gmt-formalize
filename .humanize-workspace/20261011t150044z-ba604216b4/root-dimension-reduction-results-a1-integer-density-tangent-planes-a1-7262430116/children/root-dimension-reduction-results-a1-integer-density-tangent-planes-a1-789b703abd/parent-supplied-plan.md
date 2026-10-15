# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1.square_shrink-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-789b703abd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1`
- Child key: `square_shrink`
- Declaration: `Submission.idtp_ccd_scsp_cc_square_shrink`
- Exact Lean type: `∀ (P : ℕ) (M U N₀ : Set (Euclid P)) (O : Set (Euclid 2)) (F : Euclid P → Euclid 2) (G : Euclid 2 → Euclid P) (p : Euclid P) (r₀ : ℝ), 0 < r₀ → IsOpen U → ContinuousOn F U → IsOpen O → IsOpen N₀ → F p = !₂[r₀, 0] → F p ∈ O → p ∈ N₀ → N₀ ⊆ U → G '' O = M ∩ N₀ → (∀ w ∈ O, F (G w) = w) → ∃ (s : ℝ) (N : Set (Euclid P)), 0 < s ∧ s < r₀ ∧ IsOpen N ∧ p ∈ N ∧ N ⊆ U ∧ {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s} ⊆ O ∧ M ∩ N = G '' {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
