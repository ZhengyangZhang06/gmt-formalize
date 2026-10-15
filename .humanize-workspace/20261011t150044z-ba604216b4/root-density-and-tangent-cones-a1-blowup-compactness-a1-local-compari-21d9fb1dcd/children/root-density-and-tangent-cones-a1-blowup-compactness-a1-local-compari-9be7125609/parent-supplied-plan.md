# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.series-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9be7125609/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1`
- Child key: `series`
- Declaration: `Submission.dtc_bc_lc_fd_series`
- Exact Lean type: `∀ (P k : ℕ) (X : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (X i).mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => X i ω) (Y ω)) ∧ Y.mass ≤ ∑' i, (X i).mass ∧ Y.support ⊆ closure (⋃ i, (X i).support) ∧ ((∀ i, IsIntegerMultiplicity (X i)) → IsIntegerMultiplicity Y)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
