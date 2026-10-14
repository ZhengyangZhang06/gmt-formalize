# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1.lipschitz_c1_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-8cc7497947/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1`
- Child key: `lipschitz_c1_pieces`
- Declaration: `Submission.dor_lmbsf_c1c_lipschitz_range_c1_pieces`
- Exact Lean type: `∀ (P m : ℕ) (F : Euclid m → Euclid P) (K : NNReal), LipschitzWith K F → (∀ (u : Euclid m → ℝ) (L : NNReal), LipschitzWith L u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid m → ℝ, ContDiff ℝ 1 g ∧ volume {y | u y ≠ g y} < ε) → ∃ (E : Set (Euclid P)) (G : ℕ → Euclid m → Euclid P), μHE[m] E = 0 ∧ (∀ i, ContDiff ℝ 1 (G i)) ∧ Set.range F ⊆ E ∪ ⋃ i, Set.range (G i)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
