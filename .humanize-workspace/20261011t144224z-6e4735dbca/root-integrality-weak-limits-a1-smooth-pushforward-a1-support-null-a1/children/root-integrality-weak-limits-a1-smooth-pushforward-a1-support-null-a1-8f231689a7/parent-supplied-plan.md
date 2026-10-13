# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.signed_simple_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1-8f231689a7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1`
- Child key: `signed_simple_bound`
- Declaration: `Submission.iwl_sp_sn_signed_simpleNVector_bound_ne_zero`
- Exact Lean type: `∀ (P n : ℕ) (τ : Fin n → Eucl P) (w : NVector (Eucl P) n), Orthonormal ℝ τ → (w = simpleNVector τ ∨ w = -simpleNVector τ) → (∀ b : Covector (Eucl P) n, |w b| ≤ ‖b‖) ∧ w ≠ 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
