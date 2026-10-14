# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.ambient_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4e8b16732b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`
- Child key: `ambient_calculus`
- Declaration: `Submission.idtp_fons_cc_ambient_calculus`
- Exact Lean type: `(∀ P : ℕ, IsEmbeddedSubmanifold 2 P (univ : Set (Euclid P))) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a : Euclid P) (s : ℝ) (A : Set (Euclid P)), 0 < s → MeasurableSet A → (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)) A = ENNReal.ofReal (s⁻¹ ^ n) * ν (dilation a s ⁻¹' A)) ∧ (∀ (P : ℕ) (a w : Euclid P) (s ρ : ℝ), 0 < s → dilation a s ⁻¹' ball w ρ = ball (a + s • w) (s * ρ)) ∧ (∀ (P : ℕ) (a c : Euclid P) (s ρ : ℝ), 0 < s → dilation a s '' ball c ρ = ball (dilation a s c) (ρ / s)) ∧ (∀ (P : ℕ) (a : Euclid P) (s : ℝ), 0 < s → dilation a s '' univ = univ ∧ ∀ A : Set (Euclid P), IsOpen A → IsOpen (dilation a s '' A)) ∧ (∀ (P : ℕ) (a y : Euclid P) (s t : ℝ) (A : Set (Euclid P)), 0 < s → 0 < t → dilation y t '' (dilation a s '' A) = dilation (a + s • y) (s * t) '' A) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a y : Euclid P) (s t : ℝ), 0 < s → 0 < t → ENNReal.ofReal (t⁻¹ ^ n) • (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)).map (dilation y t) = ENNReal.ofReal ((s * t)⁻¹ ^ n) • ν.map (dilation (a + s • y) (s * t))) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)), ENNReal.ofReal ((1 : ℝ)⁻¹ ^ n) • ν.map (dilation 0 1) = ν ∧ ∀ A : Set (Euclid P), dilation (0 : Euclid P) 1 '' A = A) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a : Euclid P) (s : ℝ) (B : Set (Euclid P)), 0 < s → MeasurableSet B → ENNReal.ofReal (s⁻¹ ^ n) • (ν.restrict B).map (dilation a s) = (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)).restrict (dilation a s '' B))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
