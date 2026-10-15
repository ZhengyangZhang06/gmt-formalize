# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.tangent_measure_homogeneous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-tangent-me-527431c036/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1`
- Child key: `tangent_measure_homogeneous`
- Declaration: `Submission.dimred_tr_tangent_measure_homogeneous`
- Exact Lean type: `(∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n), 1 ≤ n → n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (N = univ → ∀ (y : Euclid P) (R : ℝ), ball y R ⊆ U → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (∃ Θ : Euclid P → ℝ, (∀ y ∈ U, HasMassDensity T y (Θ y)) ∧ UpperSemicontinuousOn Θ U) ∧ ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ) → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (x : Euclid (n + k)) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ x ∈ T.support, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ ∀ R : IMRep (univ : Set (Euclid (n + k))) n, R.Represents C → ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid (n + k)), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.stationary_of_minimizing-a1`
- `root.density_and_tangent_cones-a1.blowup_density-a1`
- `root.density_and_tangent_cones-a1.cone-a1`
- `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
