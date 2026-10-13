# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.int_combination-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-int-combination-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child key: `int_combination`
- Declaration: `Submission.dor_lmb_int_combination_imrep`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ S : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n) (p₁ p₂ : ℤ), IsOpen U → R₁.Represents T₁ → R₂.Represents T₂ → (∀ ω : TestFormOn U n, S ω = (p₁ : ℝ) * T₁ ω + (p₂ : ℝ) * T₂ ω) → ∃ R : IMRep U n, R.Represents S ∧ R.measure ≤ (p₁.natAbs : ℝ≥0∞) • R₁.measure + (p₂.natAbs : ℝ≥0∞) • R₂.measure`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.tangent_locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
