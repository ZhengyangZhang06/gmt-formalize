# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1`
- Child key: `threshold_reduction`
- Declaration: `Submission.dimred_threshold_reduction`
- Exact Lean type: `∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (c : ℝ) (d₀ : ℕ) (z : Euclid (n + k)) (r : ℝ), 0 < c → 0 < r → closedBall z (2 * r) ⊆ U → (∀ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (Q : Submodule ℝ (Euclid (n + k))) (c' : ℝ), (∀ i, xs i ∈ ball z r) → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → IsMinimizingIn S univ → BoundaryVanishes S → Module.finrank ℝ Q = n → c ≤ c' → (∀ y, HasMassDensity S y (Set.indicator (Q : Set (Euclid (n + k))) (fun _ => c') y)) → False) → (∀ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (L : Submodule ℝ (Euclid (n + k))), (∀ i, xs i ∈ ball z r) → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → IsMinimizingIn S univ → BoundaryVanishes S → d₀ ≤ Module.finrank ℝ L → Module.finrank ℝ L < n → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ (w : Euclid (n + k)) (θ : ℝ), HasMassDensity S w θ → HasMassDensity S (y + lam • w) θ) → (∀ y, (∃ θ : ℝ, c ≤ θ ∧ HasMassDensity S y θ) ↔ y ∈ L) → False) → (∀ α : ℝ, 0 < α → μH[(d₀ : ℝ) - 1 + α] {x | x ∈ ball z r ∧ ∃ θ : ℝ, c ≤ θ ∧ HasMassDensity T x θ} = 0) ∧ (d₀ = 0 → {x | x ∈ ball z r ∧ ∃ θ : ℝ, c ≤ θ ∧ HasMassDensity T x θ} = ∅) ∧ (d₀ = 1 → {x | x ∈ ball z (r / 2) ∧ ∃ θ : ℝ, c ≤ θ ∧ HasMassDensity T x θ}.Finite)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.im_mass_measure-a1`
- `root.dimension_reduction_results-a1.monotonicity-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
