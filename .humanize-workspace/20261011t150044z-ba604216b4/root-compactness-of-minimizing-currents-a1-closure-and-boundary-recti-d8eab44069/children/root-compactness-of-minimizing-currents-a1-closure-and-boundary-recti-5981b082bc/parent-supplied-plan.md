# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.constant_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-5981b082bc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child key: `constant_limit`
- Declaration: `Submission.cbr_ci_bl_constant_vector_limit`
- Exact Lean type: `∀ (P n : ℕ) (Xs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (νs : ℕ → Measure (Euclid P)) (ν : Measure (Euclid P)) (μs : ℕ → Measure (Euclid P)) (τs : ℕ → Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (s : ℝ), (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → νs k K < ∞) → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x ∂(νs k)) atTop (𝓝 (∫ x, f x ∂ν))) → (∀ K : Set (Euclid P), IsCompact K → limsup (fun k => νs k K) atTop ≤ ν K) → (∀ k, AEStronglyMeasurable (τs k) (νs k)) → 0 ≤ s → (∀ α : Covector (Euclid P) n, |ζ₀ α| ≤ s * covectorEuclideanNorm α) → (∀ R : ℝ, 0 < R → Tendsto (fun k => ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k)) atTop (𝓝 0)) → (∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n), Xs k ω = ∫ x, τs k x ((ω : DifferentialForm (Euclid P) n) x) ∂(νs k)) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, C ω = ∫ x, ζ₀ ((ω : DifferentialForm (Euclid P) n) x) ∂ν) → (∀ (k : ℕ) (W : Set (Euclid P)), IsOpen W → (Xs k).massOn W = μs k W) → WeaklyConvergesOn Xs C ∧ ∀ K : Set (Euclid P), IsCompact K → limsup (fun k => μs k K) atTop ≤ ENNReal.ofReal s * ν K`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.covector_norm-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
