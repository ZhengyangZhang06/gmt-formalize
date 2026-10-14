# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.straightening_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-d52a104ed2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child key: `straightening_cover`
- Declaration: `Submission.dor_lmbsf_pc_straightening_cover`
- Exact Lean type: `∀ (n : ℕ) (F : Euclid (n + 1) → ℝ), ContDiff ℝ 1 F → ∃ (B : ℕ → Set (Euclid (n + 1))) (Ψ : ℕ → Euclid (n + 1) → Euclid (n + 1)), (∀ q, IsOpen (B q)) ∧ (∀ q, ContDiffOn ℝ 1 (Ψ q) (B q)) ∧ (∀ q, InjOn (Ψ q) (B q)) ∧ (∀ q, ∀ w ∈ B q, Bijective (fderiv ℝ (Ψ q) w)) ∧ (∀ q, ∀ w ∈ B q, F (Ψ q w) = w 0) ∧ (∀ q, IsOpen (Ψ q '' B q)) ∧ {y | fderiv ℝ F y ≠ 0} ⊆ ⋃ q, Ψ q '' B q`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.local_inverse-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
