# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.mass_le_of_forms-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1-18e28a4913/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1`
- Child key: `mass_le_of_forms`
- Declaration: `Submission.iwl_cr_cest_mass_le_of_forms`
- Exact Lean type: `∀ (P n k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) n) (C : GeometricCurrentOn (univ : Set (Eucl P)) k) (c R : ℝ), 0 ≤ c → 0 ≤ R → X.mass < ∞ → (∀ ω ∈ massAdmissibleOn (univ : Set (Eucl P)) k univ, ∀ δ : ℝ, 0 < δ → ∃ ψ : TestFormOn (univ : Set (Eucl P)) n, C ω = X ψ ∧ ∀ x, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl P) n) x) ≤ c * (R + δ)) → C.mass ≤ ENNReal.ofReal (c * R) * X.mass`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
