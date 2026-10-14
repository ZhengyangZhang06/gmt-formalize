# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-af13c47156/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1`
- Child key: `density_rep`
- Declaration: `Submission.cbr_ci_density_representation`
- Exact Lean type: `∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (η₀ : ℝ), 0 < η₀ → μ univ < ∞ → (∀ W : Set (Euclid P), IsOpen W → Γ.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → (∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0) → (∀ᵐ x ∂μ, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → ∃ (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M ∧ μHE[n] M < ∞ ∧ Measurable θ ∧ StronglyMeasurable ζ ∧ μ = (μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) ∧ (∀ x ∈ M, 0 < θ x) ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) ∧ (∀ x ∈ M, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) ∧ (∀ x ∈ M, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
