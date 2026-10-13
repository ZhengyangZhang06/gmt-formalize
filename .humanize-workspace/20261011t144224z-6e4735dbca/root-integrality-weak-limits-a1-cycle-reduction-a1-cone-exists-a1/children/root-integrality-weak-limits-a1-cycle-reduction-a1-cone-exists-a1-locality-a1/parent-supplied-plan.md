# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.locality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1-locality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1`
- Child key: `locality`
- Declaration: `Submission.iwl_cr_ce_apply_eq_of_eqOn_nhds_support`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (ψ φ : TestFormOn U n) (N : Set (Eucl P)), IsOpen N → T.support ⊆ N → (∀ x ∈ N, (ψ : DifferentialForm (Eucl P) n) x = (φ : DifferentialForm (Eucl P) n) x) → T ψ = T φ`

## Sibling prerequisites

- `root.isoperimetric-a1.vanish_off_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
