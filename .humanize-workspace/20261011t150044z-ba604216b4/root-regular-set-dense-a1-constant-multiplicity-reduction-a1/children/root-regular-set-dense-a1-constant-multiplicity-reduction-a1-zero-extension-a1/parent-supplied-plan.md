# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.constant_multiplicity_reduction-a1.zero_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-zero-extension-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1`
- Child key: `zero_extension`
- Declaration: `Submission.rsd_cmr_zero_extension`
- Exact Lean type: `∀ (P n : ℕ) (U B K : Set (Euclid P)) (hBU : B ⊆ U) (X : GeometricCurrentOn B n) (R : IMRep B n), IsOpen B → IsCompact K → K ⊆ B → R.Represents X → (∀ y ∈ B, y ∉ K → ∃ ρ : ℝ, 0 < ρ ∧ R.measure (ball y ρ) = 0) → ∃ E : GeometricCurrentOn U n, IsIntegerMultiplicity E ∧ (∀ ω : TestFormOn B n, E (testFormOnInclusion hBU n ω) = X ω) ∧ ∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → E ω = 0`

## Sibling prerequisites

- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_current-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
