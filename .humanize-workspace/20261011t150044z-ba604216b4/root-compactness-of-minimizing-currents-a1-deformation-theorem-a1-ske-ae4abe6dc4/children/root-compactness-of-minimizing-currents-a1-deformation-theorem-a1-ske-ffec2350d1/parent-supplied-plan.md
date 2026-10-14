# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1.series_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-ffec2350d1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1`
- Child key: `series_sum`
- Declaration: `Submission.cmcsdtd_deformed_series_sum`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P m : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) m), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) E → X ω = 0) → X.support ⊆ E) → (∀ (k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (W V E' K : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (H : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (Y L' : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (a b c : ℕ → ℝ≥0∞) (δ : ℝ) (K₁ K₂ K₃ : Set (Euclid P)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), HasSum (fun j => W j ω) (T ω)) → W 0 - V 0 - (E' 0 - K 0) = (H 0).boundary → (∀ j, W (j + 1) - V (j + 1) - (E' (j + 1) - (K (j + 1) - K j)) = (H (j + 1)).boundary) → (V 0).boundary = Y 0 - L' 0 → (∀ j, (V (j + 1)).boundary = Y (j + 1) - (L' (j + 1) - L' j)) → (∀ j, IsIntegerMultiplicity (V j) ∧ IsIntegerMultiplicity (H j)) → (∀ j, (V j).mass ≤ a j ∧ (H j).mass ≤ ENNReal.ofReal δ * a j ∧ (Y j).mass ≤ b j ∧ (E' j).mass ≤ ENNReal.ofReal δ * b j ∧ (L' j).mass ≤ c j ∧ (K j).mass ≤ ENNReal.ofReal δ * c j) → ∑' j, a j < ∞ → ∑' j, b j < ∞ → Tendsto c atTop (𝓝 0) → IsClosed K₁ → IsClosed K₂ → IsClosed K₃ → (∀ j, (V j).support ⊆ K₁ ∧ (H j).support ⊆ K₂ ∧ (Y j).support ⊆ K₃ ∧ (E' j).support ⊆ K₃) → ∃ (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q₀ ∧ IsIntegerMultiplicity R₁ ∧ T - Q₀ - S₁ = R₁.boundary ∧ Q₀.support ⊆ K₁ ∧ R₁.support ⊆ K₂ ∧ Q₀.boundary.support ⊆ K₃ ∧ S₁.support ⊆ K₃ ∧ Q₀.mass ≤ ∑' j, a j ∧ Q₀.boundary.mass ≤ ∑' j, b j ∧ R₁.mass ≤ ENNReal.ofReal δ * ∑' j, a j ∧ S₁.mass ≤ ENNReal.ofReal δ * ∑' j, b j`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1.telescoping_real-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1.mass_eval-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
