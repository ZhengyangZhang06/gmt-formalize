# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.weak_conv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-fe7f261e4c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1`
- Child key: `weak_conv`
- Declaration: `Submission.cmc_fcl_weakConverges_sublevel`
- Exact Lean type: `∀ (P d : ℕ) (U : Set (Euclid P)) (g : Euclid P → ℝ) (s : ℝ) (μs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P d) (ξ : Euclid P → MultiVector P d) (Ts Ts' : ℕ → GeometricCurrentOn U d) (T T' : GeometricCurrentOn U d), Continuous g → (∀ j, μs j {x | g x < s} < ∞) → μ {x | g x < s} < ∞ → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → AEStronglyMeasurable ξ μ → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) d, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) d, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ (j : ℕ) (ω : TestFormOn U d), Ts j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) d) x) ∂(μs j)) → (∀ ω : TestFormOn U d, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → (∀ (j : ℕ) (ω : TestFormOn U d), Ts' j ω = ∫ x in {x | g x < s}, ξs j x ((ω : DifferentialForm (Euclid P) d) x) ∂(μs j)) → (∀ ω : TestFormOn U d, T' ω = ∫ x in {x | g x < s}, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → WeaklyConvergesOn Ts T → (∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, μs j {x | s - δ ≤ g x ∧ g x ≤ s} ≤ ε) → WeaklyConvergesOn Ts' T'`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
