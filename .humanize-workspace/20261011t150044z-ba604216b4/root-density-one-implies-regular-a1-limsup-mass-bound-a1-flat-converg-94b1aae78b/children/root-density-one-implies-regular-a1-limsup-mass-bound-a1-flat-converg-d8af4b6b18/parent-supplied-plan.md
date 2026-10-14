# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1.order_stat-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-d8af4b6b18/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1`
- Child key: `order_stat`
- Declaration: `Submission.dor_lmb_fcdr_order_stat`
- Exact Lean type: `∀ (P m : ℕ), m + 1 < P → ∃ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, κ u ≤ u i) ∧ (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, u i ≤ κ u) ∧ ∀ u v : Fin P → ℝ, ∀ t : ℝ, (∀ i, |u i - v i| ≤ t) → |κ u - κ v| ≤ t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
