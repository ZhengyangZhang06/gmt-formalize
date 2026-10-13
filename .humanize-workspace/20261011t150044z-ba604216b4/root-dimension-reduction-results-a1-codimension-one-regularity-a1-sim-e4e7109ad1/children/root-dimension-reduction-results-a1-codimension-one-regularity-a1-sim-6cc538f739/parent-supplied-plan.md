# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.campanato_lemmas-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-6cc538f739/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `campanato_lemmas`
- Declaration: `Submission.codim1_hcp_sr_campanato_lemmas`
- Exact Lean type: `(∀ (A a b : ℝ), 0 ≤ A → 0 < b → b < a → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ (φ : ℝ → ℝ) (R₀ ε B : ℝ), 0 ≤ ε → ε ≤ ε₀ → 0 ≤ B → (∀ r : ℝ, 0 < r → r ≤ R₀ → 0 ≤ φ r) → (∀ r ρ : ℝ, 0 < r → r ≤ ρ → ρ ≤ R₀ → φ r ≤ φ ρ) → (∀ r ρ : ℝ, 0 < r → r ≤ ρ → ρ ≤ R₀ → φ r ≤ A * ((r / ρ) ^ a + ε) * φ ρ + B * ρ ^ b) → ∀ r ρ : ℝ, 0 < r → r ≤ ρ → ρ ≤ R₀ → φ r ≤ C * ((r / ρ) ^ b * φ ρ + B * r ^ b)) ∧ (∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → α ≤ 1 → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (f : Euclid m → (Euclid m →L[ℝ] Euclid k)) (x₀ : Euclid m) (R ρ₁ K : ℝ), 0 < R → 0 < ρ₁ → 0 ≤ K → ContinuousOn f (closedBall x₀ (R + ρ₁)) → (∀ x ∈ ball x₀ R, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ → ∫ z in ball x ρ, ‖f z - ⨍ z' in ball x ρ, f z'‖ ^ 2 ≤ K * ρ ^ ((m : ℝ) + 2 * α)) → ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ‖x - y‖ ≤ ρ₁ / 2 → ‖f x - f y‖ ≤ C₀ * Real.sqrt K * ‖x - y‖ ^ α)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
