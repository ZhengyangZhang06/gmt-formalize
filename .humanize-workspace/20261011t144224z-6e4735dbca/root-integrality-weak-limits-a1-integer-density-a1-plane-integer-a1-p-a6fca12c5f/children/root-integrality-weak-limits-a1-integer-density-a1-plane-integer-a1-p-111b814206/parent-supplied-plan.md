# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.projected_limit-a1.linear_pushforward_family-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-p-111b814206/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.projected_limit-a1`
- Child key: `linear_pushforward_family`
- Declaration: `Submission.ind_pi_pl_linear_pushforward_family`
- Exact Lean type: `LipschitzPushforwardIntegerMultiplicity → (LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V → ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q), IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧ (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (k + 1)) x = ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η) ∧ (∀ (ω : TestFormOn V k) (η : TestFormOn U k), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S.boundary ω = X.boundary η) ∧ ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧ S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U)) → ∀ (P Q m : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (F : Set (Eucl P)) (p : Eucl P →L[ℝ] Eucl Q) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → IsOpen V → ‖p‖ ≤ 1 → MapsTo p U V → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (p ⁻¹' K ∩ F) ∧ p ⁻¹' K ∩ F ⊆ U) → (∀ k, IsIntegerMultiplicity (X k)) → (∀ k, (X k).support ⊆ F) → ∃ S : ℕ → GeometricCurrentOn V (m + 1), (∀ k, IsIntegerMultiplicity (S k)) ∧ (∀ (k : ℕ) (ω : TestFormOn V (m + 1)) (η : TestFormOn U (m + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ (X k).support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (m + 1)) x = ((ω : DifferentialForm (Eucl Q) (m + 1)) (p x)).compContinuousLinearMap p) → S k ω = X k η) ∧ ∀ (k : ℕ) (W : Set (Eucl Q)), (S k).massOn W ≤ (X k).mass ∧ (S k).boundary.massOn W ≤ (X k).boundary.mass`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
