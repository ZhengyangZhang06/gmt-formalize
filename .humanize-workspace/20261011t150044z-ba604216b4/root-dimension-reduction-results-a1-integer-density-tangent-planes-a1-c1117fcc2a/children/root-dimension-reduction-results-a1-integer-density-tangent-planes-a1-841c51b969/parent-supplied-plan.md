# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1.imrep_construction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-841c51b969/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1`
- Child key: `imrep_construction`
- Declaration: `Submission.idtp_fons_odc_pc_imrep`
- Exact Lean type: `∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℤ), (∀ k, ‖v k‖ = 1) → (∀ k, IsOpen (I k)) → (∀ j k, j ≠ k → (μHE[1] : Measure (Euclid P)) (((fun t : ℝ => p j + t • v j) '' I j) ∩ closure ((fun t : ℝ => p k + t • v k) '' I k)) = 0) → ∃ R : IMRep (univ : Set (Euclid P)) 1, R.carrier = (⋃ k, ⋃ (_ : c k ≠ 0), (fun t : ℝ => p k + t • v k) '' I k) ∧ (∀ x, R.mult x = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k).natAbs) x) ∧ ∀ (x : Euclid P) (α : Covector (Euclid P) 1), (R.mult x : ℝ) * R.orient x α = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k : ℝ)) x * α (fun _ => v k)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1.local_plane_tangent-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1.piece_locally_line-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
