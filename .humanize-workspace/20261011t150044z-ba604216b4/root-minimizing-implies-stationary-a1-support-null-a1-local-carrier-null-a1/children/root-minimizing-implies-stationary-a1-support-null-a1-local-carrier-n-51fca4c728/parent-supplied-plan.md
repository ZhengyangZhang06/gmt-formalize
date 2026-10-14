# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.support_null-a1.local_carrier_null-a1.orient_component_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1-local-carrier-n-51fca4c728/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.support_null-a1.local_carrier_null-a1`
- Child key: `orient_component_null`
- Declaration: `Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → ∀ α : Covector (Euclid P) n, ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x α = 0`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.support_null-a1.local_carrier_null-a1.component_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
