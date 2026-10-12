# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.rescale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1`
- Child key: `rescale`
- Declaration: `Submission.ind_rescaled_current`
- Exact Lean type: `∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (x : Eucl P) (r : ℝ), 0 < r → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), (∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1), ∃ η : TestFormOn (univ : Set (Eucl P)) (m + 1), ∀ y, (η : DifferentialForm (Eucl P) (m + 1)) y = (r ^ (m + 1))⁻¹ • (ω : DifferentialForm (Eucl P) (m + 1)) (r⁻¹ • (y - x))) ∧ (∀ ω η : TestFormOn (univ : Set (Eucl P)) (m + 1), (∀ y, (η : DifferentialForm (Eucl P) (m + 1)) y = (r ^ (m + 1))⁻¹ • (ω : DifferentialForm (Eucl P) (m + 1)) (r⁻¹ • (y - x))) → Y ω = X η) ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) ∧ (X.boundary = 0 → Y.boundary = 0) ∧ ∀ W : Set (Eucl P), Y.massOn W ≤ ENNReal.ofReal ((r ^ (m + 1))⁻¹) * X.massOn {y | r⁻¹ • (y - x) ∈ W}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
