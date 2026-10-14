# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-imrep-restrict-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1`
- Child key: `imrep_restrict`
- Declaration: `Submission.rsd_cmr_imrep_restrict`
- Exact Lean type: `∀ (P n : ℕ) (U U' A : Set (Euclid P)) (R : IMRep U n) (θ : Euclid P → ℕ), MeasurableSet A → R.carrier ∩ A ⊆ U' → Measurable θ → (∀ x ∈ R.carrier ∩ A, 0 < θ x) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U' → ∫⁻ x in R.carrier ∩ A ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ A)), ∃ δ : ℝ, 0 < δ ∧ μHE[n] ((R.carrier \ A) ∩ ball x δ) = 0) → ∃ R' : IMRep U' n, R'.carrier = R.carrier ∩ A ∧ R'.mult = θ ∧ R'.orient = R.orient`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
