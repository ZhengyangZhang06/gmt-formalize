# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_sard-a1.jacobian_rank-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-sard-a1-jacobian-rank-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_sard-a1`
- Child key: `jacobian_rank`
- Declaration: `Submission.c1_sard_coarea_jacobian_eq_zero_iff`
- Exact Lean type: `∀ (N m : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N), coareaJacobian M f x = 0 ↔ Module.finrank ℝ (LinearMap.range ((fderiv ℝ f x).toLinearMap ∘ₗ (tangentSpace M x).subtype)) < m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
