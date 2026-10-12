# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1.approx_tangent_local-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-c1-submani-e8366cd9c8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1`
- Child key: `approx_tangent_local`
- Declaration: `Submission.rsod_c1tan_approxTangent_of_local_eq`
- Exact Lean type: `∀ (m N : ℕ) (S T : Set (EuclideanSpace ℝ (Fin N))) (x : EuclideanSpace ℝ (Fin N)) (ε : ℝ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))), 0 < ε → S ∩ ball x ε = T ∩ ball x ε → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt m T x P → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt m S x P`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
