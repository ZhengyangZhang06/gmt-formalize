# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1.cube_skeleton-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-8144f77fee/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1`
- Child key: `cube_skeleton`
- Declaration: `Submission.dor_lmb_fcdr_cube_skeleton`
- Exact Lean type: `∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, κ u ≤ u i) → ∀ Φ : Euclid P → Euclid P, (∀ (y : Euclid P) (i : Fin P), Φ y i = a i + (y i - a i) / max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)))) → ∀ y : Euclid P, 0 < κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) → (∀ i, 0 ≤ Φ y i ∧ Φ y i ≤ 1) ∧ ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, Φ y i = 0 ∨ Φ y i = 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
