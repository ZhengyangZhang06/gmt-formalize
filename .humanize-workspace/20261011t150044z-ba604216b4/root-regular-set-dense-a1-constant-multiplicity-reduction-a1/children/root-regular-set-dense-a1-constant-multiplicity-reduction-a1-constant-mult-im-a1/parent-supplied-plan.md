# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.constant_multiplicity_reduction-a1.constant_mult_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-constant-mult-im-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1`
- Child key: `constant_mult_im`
- Declaration: `Submission.rsd_cmr_isIntegerMultiplicity_of_const_mult`
- Exact Lean type: `∀ (P n : ℕ) (U V : Set (Euclid P)) (hVU : V ⊆ U) (T : GeometricCurrentOn U n) (R : IMRep U n) (T₀ : GeometricCurrentOn V n) (N₀ : ℕ), IsOpen V → 0 < N₀ → R.Represents T → (∀ᵐ x ∂R.measure, x ∈ V → R.mult x = N₀) → (∀ ω : TestFormOn V n, T (testFormOnInclusion hVU n ω) = (N₀ : ℝ) * T₀ ω) → IsIntegerMultiplicity T₀`

## Sibling prerequisites

- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_restrict-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
