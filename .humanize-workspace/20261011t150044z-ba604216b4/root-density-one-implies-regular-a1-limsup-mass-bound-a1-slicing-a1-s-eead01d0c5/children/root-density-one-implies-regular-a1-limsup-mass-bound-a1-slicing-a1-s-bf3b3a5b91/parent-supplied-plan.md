# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.left_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-bf3b3a5b91/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child key: `left_inverse`
- Declaration: `Submission.dor_lmbsf_pwl_immersion_left_inverse`
- Exact Lean type: `∀ (P d : ℕ) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ∃ R : Euclid d → (Euclid P →L[ℝ] Euclid d), ContinuousOn R V ∧ ∀ y ∈ V, (R y).comp (fderiv ℝ ψ y) = ContinuousLinearMap.id ℝ (Euclid d)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
