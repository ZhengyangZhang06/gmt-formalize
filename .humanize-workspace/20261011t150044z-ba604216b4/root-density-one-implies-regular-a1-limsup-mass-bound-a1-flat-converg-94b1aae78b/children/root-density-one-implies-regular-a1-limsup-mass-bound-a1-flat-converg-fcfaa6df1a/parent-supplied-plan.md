# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1.grid_segment-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-fcfaa6df1a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1`
- Child key: `grid_segment`
- Declaration: `Submission.dor_lmb_fcdr_grid_segment`
- Exact Lean type: `∀ (P : ℕ) (f : Euclid P → Euclid P) (S : Set (Euclid P)) (K : ℝ), 0 ≤ K → (∀ (z : Fin P → ℤ) (x y : Euclid P), x ∈ S → y ∈ S → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → (∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1) → dist (f x) (f y) ≤ K * dist x y) → ∀ x y : Euclid P, segment ℝ x y ⊆ S → dist (f x) (f y) ≤ K * dist x y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
