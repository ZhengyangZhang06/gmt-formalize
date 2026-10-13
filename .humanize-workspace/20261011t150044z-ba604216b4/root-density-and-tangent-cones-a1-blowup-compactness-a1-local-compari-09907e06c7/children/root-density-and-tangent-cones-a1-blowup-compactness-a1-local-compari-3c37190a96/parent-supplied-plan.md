# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.c1_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-3c37190a96/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`
- Child key: `c1_tangent`
- Declaration: `Submission.dtc_bc_lc_sl_c1_tangent`
- Exact Lean type: `∀ (P d : ℕ) (g : Euclid d → Euclid P) (U : Set (Euclid d)) (c : Euclid d) (r : ℝ), IsOpen U → closedBall c r ⊆ U → ContDiffOn ℝ 1 g U → InjOn g (closedBall c r) → (∀ z ∈ closedBall c r, Injective (fderiv ℝ g z)) → ∀ z ∈ ball c r, HasApproximateTangentSpaceAt d (g '' closedBall c r) (g z) (LinearMap.range (fderiv ℝ g z : Euclid d →ₗ[ℝ] Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
