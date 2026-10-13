# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.carrier_facts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-f5067fe842/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1`
- Child key: `carrier_facts`
- Declaration: `Submission.dimred_mbl_pf_imrep_carrier_mass_support`
- Exact Lean type: `∀ (P n : ℕ), (∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), R.Represents Y → μHE[n] (R.carrier \ Y.support) = 0 ∧ Y.mass = R.measure univ ∧ (IsCompact Y.support → R.measure univ ≠ ∞)) ∧ ∀ Y₁ Y₂ : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed Y₁.support ∧ (Y₁ - Y₂).support ⊆ Y₁.support ∪ Y₂.support`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
