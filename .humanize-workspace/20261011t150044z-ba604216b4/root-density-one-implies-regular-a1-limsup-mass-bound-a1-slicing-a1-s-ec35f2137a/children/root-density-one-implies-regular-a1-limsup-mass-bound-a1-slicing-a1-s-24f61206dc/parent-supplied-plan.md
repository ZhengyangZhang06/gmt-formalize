# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.gram_cofactor-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-24f61206dc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child key: `gram_cofactor`
- Declaration: `Submission.dor_lmbsf_pc_gram_det_succ_eq`
- Exact Lean type: `∀ (P n : ℕ) (a : Fin (n + 1) → Euclid P) (u : Euclid P), u ∈ Submodule.span ℝ (Set.range a) → inner ℝ u (a 0) = 1 → (∀ k : Fin n, inner ℝ u (a k.succ) = 0) → Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (a i.succ) (a j.succ)) = ‖u‖ ^ 2 * Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (a i) (a j))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
