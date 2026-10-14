# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1.dual_dist-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-2c688a1d91/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1`
- Child key: `dual_dist`
- Declaration: `Submission.dor_lmb_fcdr_dual_dist`
- Exact Lean type: `∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, u i ≤ κ u) → ∀ x y : Euclid P, (∀ i, ∃ k : ℤ, x i - y i = k) → infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} ≤ Real.sqrt (m + 2) * κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
