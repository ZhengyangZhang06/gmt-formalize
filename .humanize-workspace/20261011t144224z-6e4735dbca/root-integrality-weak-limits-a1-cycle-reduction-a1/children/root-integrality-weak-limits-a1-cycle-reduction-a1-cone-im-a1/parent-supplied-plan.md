# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1`
- Child key: `cone_im`
- Declaration: `Submission.iwl_cr_cone_integer_multiplicity`
- Exact Lean type: `∀ (P m : ℕ), (∀ (Z : GeometricCurrentOn (univ : Set (Eucl (P + 1))) (m + 1)) (f : Eucl (P + 1) → Eucl P), IsIntegerMultiplicity Z → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ K : Set (Eucl P), IsCompact K → IsCompact (f ⁻¹' K ∩ Z.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), IsIntegerMultiplicity S ∧ ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)), (∃ N : Set (Eucl (P + 1)), IsOpen N ∧ Z.support ⊆ N ∧ ∀ y ∈ N, (η : DifferentialForm (Eucl (P + 1)) (m + 1)) y = ((ω : DifferentialForm (Eucl P) (m + 1)) (f y)).compContinuousLinearMap (fderiv ℝ f y)) → S ω = Z η) → ∀ (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), IsIntegerMultiplicity X → X.support ⊆ closedBall 0 R → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → IsIntegerMultiplicity C`

## Sibling prerequisites

- `root.isoperimetric-a1.vanish_off_support-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
