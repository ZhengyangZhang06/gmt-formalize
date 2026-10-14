# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-1351bbab52/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child key: `c1_cover`
- Declaration: `Submission.dor_lmbsf_rectifiable_c1_cover`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Euclid P)), CountablyRectifiable m M → ∃ (N₀ : Set (Euclid P)) (N : ℕ → Set (Euclid P)), μHE[m] N₀ = 0 ∧ (∀ l, IsEmbeddedSubmanifold 1 m (N l)) ∧ M ⊆ N₀ ∪ ⋃ l, N l`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
