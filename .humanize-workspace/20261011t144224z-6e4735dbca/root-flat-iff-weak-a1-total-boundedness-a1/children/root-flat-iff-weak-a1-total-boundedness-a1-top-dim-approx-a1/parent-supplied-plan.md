# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child key: `top_dim_approx`
- Declaration: `Submission.fiw_tb_top_dim_approx`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ), IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S) → ∀ m : ℕ, ∃ c : ℝ≥0, ∀ X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1), IsIntegerMultiplicity X → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ρ : ℝ, 0 < ρ → ∃ (β : LatticeFaceIndex (m + 1) (m + 1) → ℝ) (Pc S : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsLatticeChain ρ β Pc ∧ (∀ F, ∃ k : ℤ, β F = k) ∧ (∀ F, β F ≠ 0 → latticeFace ρ F ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ) X.support) ∧ (∀ F, ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ 2 * X.mass) ∧ IsIntegerMultiplicity S ∧ (∀ ω, X ω - Pc ω = S ω) ∧ S.mass ≤ c * ENNReal.ofReal ρ * X.boundary.mass`

## Sibling prerequisites

- `root.flat_iff_weak-a1.total_boundedness-a1.support_null-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
