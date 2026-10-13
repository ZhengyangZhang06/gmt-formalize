# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.projected_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-p-a6fca12c5f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1`
- Child key: `projected_limit`
- Declaration: `Submission.ind_pi_projected_limit`
- Exact Lean type: `LipschitzPushforwardIntegerMultiplicity → (LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V → ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q), IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧ (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (k + 1)) x = ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η) ∧ (∀ (ω : TestFormOn V k) (η : TestFormOn U k), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S.boundary ω = X.boundary η) ∧ ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧ S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U)) → ∀ (P m : ℕ) (τ : Fin (m + 1) → Eucl P) (c γ : ℝ) (p : Eucl P →L[ℝ] Eucl (m + 1)) (d : Eucl P → ℝ) (Z : ℕ → GeometricCurrentOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1)) (S : GeometricCurrentOn (ball (0 : Eucl (m + 1)) 1) (m + 1)), Orthonormal ℝ τ → (∀ y i, p y i = inner ℝ (τ i) y) → (∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖) → 0 ≤ γ → γ < 3 / 4 → (∀ k, IsIntegerMultiplicity (Z k)) → (∀ k, (Z k).support ⊆ {y | d y ≤ γ}) → (⨆ k, ((Z k).mass + (Z k).boundary.mass)) < ∞ → (∀ ω : TestFormOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1), Tendsto (fun k => Z k ω) atTop (𝓝 (c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P))))) → (∀ ω : TestFormOn (ball (0 : Eucl (m + 1)) 1) (m + 1), S ω = c * ∫ x in ball (0 : Eucl (m + 1)) 1, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) → ∃ S' : ℕ → GeometricCurrentOn (ball (0 : Eucl (m + 1)) 1) (m + 1), (∀ k, IsIntegerMultiplicity (S' k)) ∧ (∀ W, CompactlyContainedOpen W (ball (0 : Eucl (m + 1)) 1) → (⨆ k, ((S' k).massOn W + (S' k).boundary.massOn W)) < ∞) ∧ WeaklyConvergesOn S' S`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.frame_geometry-a1`
- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.span_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
