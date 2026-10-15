# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.series_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-802e76d13c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1`
- Child key: `series_limit`
- Declaration: `Submission.dor_lmb_fc_series_limit`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)) (Xlim : GeometricCurrentOn U (m + 1)) (R : ℕ → GeometricCurrentOn U (m + 2)) (S : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → WeaklyConvergesOn X Xlim → (∀ r, IsIntegerMultiplicity (R r) ∧ IsIntegerMultiplicity (S r) ∧ (∀ ω : TestFormOn U (m + 1), X (r + 1) ω - X r ω = (R r).boundary ω + S r ω) ∧ (R r).mass + (S r).mass ≤ (2⁻¹ : ℝ≥0∞) ^ r) → ∀ ℓ : ℕ, ∃ (R' : GeometricCurrentOn U (m + 2)) (S' : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R' ∧ IsIntegerMultiplicity S' ∧ (∀ ω : TestFormOn U (m + 1), Xlim ω - X ℓ ω = R'.boundary ω + S' ω) ∧ R'.mass + S'.mass ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ ℓ`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
