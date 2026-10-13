# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_limit-a1.im_partial_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-series-b770db587f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_limit-a1`
- Child key: `im_partial_sum`
- Declaration: `Submission.cmc_fc_sl_im_partial_sum`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (Y : ℕ → GeometricCurrentOn U n), (∀ A B : GeometricCurrentOn U n, IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → (∀ i, IsIntegerMultiplicity (Y i)) → ∀ N : ℕ, ∃ Z : GeometricCurrentOn U n, IsIntegerMultiplicity Z ∧ (∀ ω : TestFormOn U n, Z ω = ∑ i ∈ Finset.range (N + 1), Y i ω) ∧ ∀ G : Set (Euclid P), Z.massOn G ≤ ∑ i ∈ Finset.range (N + 1), (Y i).massOn G`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_limit-a1.mass_triangle-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
