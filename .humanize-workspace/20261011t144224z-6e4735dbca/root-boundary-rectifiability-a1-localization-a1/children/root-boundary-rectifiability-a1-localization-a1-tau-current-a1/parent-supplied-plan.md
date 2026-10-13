# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.localization-a1.tau_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1-tau-current-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.localization-a1`
- Child key: `tau_current`
- Declaration: `Submission.br_loc_tauAction_current`
- Exact Lean type: `∀ (P n : ℕ) (V M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple V n M θ ξ → ∃ X : GeometricCurrentOn V n, ∀ ω : TestFormOn V n, X ω = tauAction n M θ ξ ω`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_integrable-a1`
- `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.unit_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
