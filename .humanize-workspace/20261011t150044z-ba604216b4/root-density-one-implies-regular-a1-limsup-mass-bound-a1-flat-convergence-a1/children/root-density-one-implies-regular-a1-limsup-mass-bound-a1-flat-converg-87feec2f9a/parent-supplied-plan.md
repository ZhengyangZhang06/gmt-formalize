# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.cauchy_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-87feec2f9a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1`
- Child key: `cauchy_subseq`
- Declaration: `Submission.dor_lmb_fc_cauchy_subseq`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ ε : ℝ≥0∞, 0 < ε → ∃ 𝒬 : Set (GeometricCurrentOn U (m + 1)), 𝒬.Finite ∧ ∀ j, ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω : TestFormOn U (m + 1), X j ω - Q ω = R.boundary ω + S ω) ∧ R.mass + S.mass < ε) → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ r, ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω : TestFormOn U (m + 1), X (θ (r + 1)) ω - X (θ r) ω = R.boundary ω + S ω) ∧ R.mass + S.mass ≤ (2⁻¹ : ℝ≥0∞) ^ r`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
