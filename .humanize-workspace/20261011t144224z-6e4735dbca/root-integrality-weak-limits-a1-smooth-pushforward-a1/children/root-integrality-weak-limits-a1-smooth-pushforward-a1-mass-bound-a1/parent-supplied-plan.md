# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.smooth_pushforward-a1.mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`
- Child key: `mass_bound`
- Declaration: `Submission.iwl_sp_massOn_le_of_compatible`
- Exact Lean type: `∀ (P Q j : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (A : Set (Eucl P)) (Y : GeometricCurrentOn V j) (Z : GeometricCurrentOn U j) (f : Eucl P → Eucl Q) (c : ℝ), IsOpen U → A ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ A)) → (∀ (ω : TestFormOn V j) (η : TestFormOn U j), (∃ N : Set (Eucl P), IsOpen N ∧ A ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) j) x = ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → Y ω = Z η) → 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), Y.massOn W ≤ ENNReal.ofReal (c ^ j) * Z.massOn (f ⁻¹' W ∩ U)`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1`
- `root.integrality_weak_limits-a1.smooth_pushforward-a1.compatible_form-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
