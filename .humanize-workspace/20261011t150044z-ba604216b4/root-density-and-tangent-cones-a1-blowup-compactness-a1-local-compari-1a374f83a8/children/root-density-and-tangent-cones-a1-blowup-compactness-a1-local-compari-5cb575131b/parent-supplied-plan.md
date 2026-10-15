# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.immersion_antilipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-5cb575131b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child key: `immersion_antilipschitz`
- Declaration: `Submission.dtc_bc_lc_sl_ll_immersion_antilipschitz`
- Exact Lean type: `∀ (P N : ℕ) (ψ : Euclid N → Euclid P) (C : Set (Euclid N)), ContDiff ℝ 1 ψ → IsCompact C → InjOn ψ C → (∀ y ∈ C, Injective (fderiv ℝ ψ y)) → ∃ c : ℝ, 0 < c ∧ ∀ a ∈ C, ∀ b ∈ C, c * ‖a - b‖ ≤ ‖ψ a - ψ b‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
