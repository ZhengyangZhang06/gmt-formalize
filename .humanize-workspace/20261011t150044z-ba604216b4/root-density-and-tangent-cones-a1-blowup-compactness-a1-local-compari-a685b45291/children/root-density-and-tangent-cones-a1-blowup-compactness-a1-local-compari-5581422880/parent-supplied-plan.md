# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.carrier_facts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-5581422880/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1`
- Child key: `carrier_facts`
- Declaration: `Submission.dtc_bc_lc_pf_imrep_carrier_mass_support`
- Exact Lean type: `∀ (P n : ℕ), (∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), R.Represents Y → μHE[n] (R.carrier \ Y.support) = 0 ∧ Y.mass = R.measure univ ∧ (IsCompact Y.support → R.measure univ ≠ ∞)) ∧ ∀ Y₁ Y₂ : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed Y₁.support ∧ (Y₁ - Y₂).support ⊆ Y₁.support ∪ Y₂.support`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
