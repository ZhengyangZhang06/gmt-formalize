# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1.imrep_zero_structure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-zero-dim-minimizing-trivial-a1-im-4b50b377f9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1`
- Child key: `imrep_zero_structure`
- Declaration: `Submission.dor_zdm_imrep_zero_structure`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (R : IMRep U 0), R.carrier.Countable ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → (R.carrier ∩ K).Finite ∧ R.measure K ≠ ∞) ∧ (∀ x ∈ R.carrier, (∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt 0 R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q) ∧ R.orient x ≠ 0) ∧ (IsOpen U → U ∩ R.measure.support = R.carrier)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
