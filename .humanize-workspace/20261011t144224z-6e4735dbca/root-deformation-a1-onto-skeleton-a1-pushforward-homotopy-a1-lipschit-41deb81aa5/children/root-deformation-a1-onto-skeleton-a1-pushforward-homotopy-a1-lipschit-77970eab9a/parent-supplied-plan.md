# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1.bounded_compatible-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-77970eab9a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1`
- Child key: `bounded_compatible`
- Declaration: `Submission.dph_lpfex_bounded_compatible_form`
- Exact Lean type: `∀ (m m' k : ℕ) (f : Eucl m → Eucl m') (A O : Set (Eucl m)) (Λ : ℝ≥0), IsOpen O → A ⊆ O → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ x ∈ O, ‖fderiv ℝ f x‖ ≤ Λ) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (f ⁻¹' K ∩ A)) → ∀ ω : TestFormOn (univ : Set (Eucl m')) k, ∃ η : TestFormOn (univ : Set (Eucl m)) k, (∃ N : Set (Eucl m), IsOpen N ∧ A ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∧ ∀ C : ℝ, (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) y) ≤ C) → ∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl m) k) x) ≤ (Λ : ℝ) ^ k * C`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.compatible_form-a1`
- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
