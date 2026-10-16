# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1.piece_locally_line-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2a055a4c1e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1`
- Child key: `piece_locally_line`
- Declaration: `Submission.idtp_fons_odc_pc_piece_locally_line`
- Exact Lean type: `∀ (P : ℕ) (ι : Type) [Finite ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (M : Set (Euclid P)) (k : ι) (x : Euclid P), ‖v k‖ = 1 → IsOpen (I k) → M ⊆ (⋃ j, (fun t : ℝ => p j + t • v j) '' I j) → (fun t : ℝ => p k + t • v k) '' I k ⊆ M → x ∈ (fun t : ℝ => p k + t • v k) '' I k → (∀ j, j ≠ k → x ∉ closure ((fun t : ℝ => p j + t • v j) '' I j)) → ∃ r : ℝ, 0 < r ∧ M ∩ ball x r = {y | y - x ∈ Submodule.span ℝ {v k}} ∩ ball x r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
