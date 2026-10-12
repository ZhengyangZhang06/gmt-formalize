# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-c1-submani-3373b6823b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- Child key: `c1_submanifold_tangent`
- Declaration: `Submission.rsod_isC1Submanifold_approxTangent`
- Exact Lean type: `∀ (m N : ℕ), 1 ≤ m → ∀ (S : Set (EuclideanSpace ℝ (Fin N))), IsC1Submanifold m S → ∀ x ∈ S, ∃ P : Submodule ℝ (EuclideanSpace ℝ (Fin N)), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt m S x P`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
