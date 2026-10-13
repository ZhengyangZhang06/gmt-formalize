# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6c861e5511/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1`
- Child key: `constant_planes`
- Declaration: `Submission.cbr_ci_constant_cycle_planes`
- Exact Lean type: `∀ (P d : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P (d + 1)) (c : ℝ), 0 < c → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ β : Covector (Euclid P) (d + 1), |ζ₀ β| ≤ covectorEuclideanNorm β) → (∃ β : Covector (Euclid P) (d + 1), covectorEuclideanNorm β ≤ 1 ∧ ζ₀ β = 1) → (∀ φ : TestFormOn (univ : Set (Euclid P)) d, ∫ y, ζ₀ (exteriorDerivative (φ : DifferentialForm (Euclid P) d) y) ∂ν = 0) → (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ unitBallVolume (d + 1) * ENNReal.ofReal (R ^ (d + 1))) → (∀ r : ℝ, 0 < r → 0 < ν (ball 0 r)) → (∀ᵐ y ∂ν, ENNReal.ofReal c ≤ liminf (fun r : ℝ => ν (ball y r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0)) → ∃ (v : Fin (d + 1) → Euclid P) (N : ℕ) (w : Fin N → Euclid P) (α : Fin N → ℝ), Orthonormal ℝ v ∧ (∀ β : Covector (Euclid P) (d + 1), ζ₀ β = β v) ∧ Injective w ∧ (∀ (i : Fin N) (j : Fin (d + 1)), inner ℝ (w i) (v j) = 0) ∧ (∀ i, c ≤ α i) ∧ ∑ i, α i ≤ 1 ∧ (∃ i, w i = 0) ∧ ν = ∑ i, ENNReal.ofReal (α i) • (μHE[(d + 1)]).restrict {y : Euclid P | y - w i ∈ Submodule.span ℝ (Set.range v)}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
