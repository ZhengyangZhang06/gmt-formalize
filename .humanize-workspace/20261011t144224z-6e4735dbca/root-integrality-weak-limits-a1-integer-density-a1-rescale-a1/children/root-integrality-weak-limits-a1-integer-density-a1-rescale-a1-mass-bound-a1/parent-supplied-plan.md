# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1`
- Child key: `mass_bound`
- Declaration: `Submission.ind_rs_massOn_dilation_le`
- Exact Lean type: `∀ (P n : ℕ) (X Y : GeometricCurrentOn (univ : Set (Eucl P)) n) (x : Eucl P) (r : ℝ), 0 < r → (∀ ω : TestFormOn (univ : Set (Eucl P)) n, ∃ η : TestFormOn (univ : Set (Eucl P)) n, ∀ y, (η : DifferentialForm (Eucl P) n) y = (r ^ n)⁻¹ • (ω : DifferentialForm (Eucl P) n) (r⁻¹ • (y - x))) → (∀ ω η : TestFormOn (univ : Set (Eucl P)) n, (∀ y, (η : DifferentialForm (Eucl P) n) y = (r ^ n)⁻¹ • (ω : DifferentialForm (Eucl P) n) (r⁻¹ • (y - x))) → Y ω = X η) → ∀ W : Set (Eucl P), Y.massOn W ≤ ENNReal.ofReal ((r ^ n)⁻¹) * X.massOn {y | r⁻¹ • (y - x) ∈ W}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
