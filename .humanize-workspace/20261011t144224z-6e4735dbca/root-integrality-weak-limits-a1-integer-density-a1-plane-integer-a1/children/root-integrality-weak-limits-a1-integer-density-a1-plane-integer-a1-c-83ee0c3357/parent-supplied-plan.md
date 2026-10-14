# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.const_vector_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-c-83ee0c3357/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1`
- Child key: `const_vector_current`
- Declaration: `Submission.ind_pi_constant_vector_current`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (w : NVector (Eucl P) n), (∀ K : Set (Eucl P), IsCompact K → μ K < ∞) → ∃ T : GeometricCurrentOn U n, IsMeasureRepresentation T μ (fun _ => w)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
