# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.constant_multiplicity_reduction-a1.cutoff_vanishing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-cutoff-vanishing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1`
- Child key: `cutoff_vanishing`
- Declaration: `Submission.rsd_cmr_eq_zero_of_vanish_off_compact`
- Exact Lean type: `∀ (P m : ℕ) (U B K : Set (Euclid P)) (hBU : B ⊆ U) (F : GeometricCurrentOn U m), IsOpen B → IsCompact K → K ⊆ B → (∀ ω : TestFormOn U m, Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) K → F ω = 0) → (∀ ψ : TestFormOn B m, F (testFormOnInclusion hBU m ψ) = 0) → ∀ ω : TestFormOn U m, F ω = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
