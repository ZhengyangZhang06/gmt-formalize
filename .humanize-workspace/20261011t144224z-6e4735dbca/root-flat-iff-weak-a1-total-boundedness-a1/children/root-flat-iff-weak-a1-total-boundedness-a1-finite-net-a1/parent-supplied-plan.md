# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.finite_net-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-finite-net-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child key: `finite_net`
- Declaration: `Submission.fiw_tb_finite_net`
- Exact Lean type: `DeformationTheorem → (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ), IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S) → ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (K : Set (Eucl P)), IsCompact K → K ⊆ U → ∃ C : ℝ≥0, ∀ (B : ℝ≥0∞), B ≠ ∞ → ∀ ρ : ℝ, 0 < ρ → ∃ Qs : Set (GeometricCurrentOn U (m + 1)), Qs.Finite ∧ ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → T.support ⊆ K → T.mass + T.boundary.mass ≤ B → ∃ Q ∈ Qs, ∃ (R : GeometricCurrentOn U (m + 1 + 1)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω, T ω - Q ω = R.boundary ω + S ω) ∧ R.mass + S.mass ≤ C * ENNReal.ofReal ρ * B`

## Sibling prerequisites

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.restrict_im-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.lattice_coeff_finite-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
