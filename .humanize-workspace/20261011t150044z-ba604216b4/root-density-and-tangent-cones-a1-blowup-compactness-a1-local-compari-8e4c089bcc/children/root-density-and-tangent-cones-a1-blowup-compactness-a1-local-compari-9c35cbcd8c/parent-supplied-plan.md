# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.closure_cycles-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9c35cbcd8c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1`
- Child key: `closure_cycles`
- Declaration: `Submission.dtc_bc_lc_fd_bim_closure_cycles`
- Exact Lean type: `∀ (P n : ℕ) (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n) (T : GeometricCurrentOn (univ : Set (Euclid P)) n), n < P → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ j, BoundaryVanishes (Ts j)) → ⨆ j, (Ts j).mass < ∞ → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
