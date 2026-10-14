# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`
- Child key: `density`
- Declaration: `Submission.fiw_tb_tda_density`
- Exact Lean type: `∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsIntegerMultiplicity X → X.mass < ∞ → (∀ (M : Set (Eucl (m + 1))) (θ : Eucl (m + 1) → ℝ) (ξ : Eucl (m + 1) → NVector (Eucl (m + 1)) (m + 1)), IsRectifiableTriple (univ : Set (Eucl (m + 1))) (m + 1) M θ ξ → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = tauAction (m + 1) M θ ξ ω) → X.mass = ∫⁻ x in M, ENNReal.ofReal (θ x) ∂(μHE[m + 1] : Measure (Eucl (m + 1))) ∧ (μHE[m + 1] : Measure (Eucl (m + 1))) (M \ X.support) = 0) → ∃ u : Eucl (m + 1) → ℝ, Measurable u ∧ (∀ x, ∃ k : ℤ, u x = k) ∧ Integrable u ∧ ∫⁻ x, ENNReal.ofReal |u x| = X.mass ∧ (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∉ X.support → u x = 0) ∧ ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = ∫ x, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
