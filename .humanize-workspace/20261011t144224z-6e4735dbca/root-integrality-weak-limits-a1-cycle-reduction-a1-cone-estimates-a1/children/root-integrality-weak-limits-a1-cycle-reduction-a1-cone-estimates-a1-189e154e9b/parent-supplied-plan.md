# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.cutoff_radial_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1-189e154e9b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1`
- Child key: `cutoff_radial_form`
- Declaration: `Submission.iwl_cr_cest_cutoff_radial_form`
- Exact Lean type: `∀ (P m : ℕ) (ω : DifferentialForm (Eucl P) (m + 1)) (ψ₀ : DifferentialForm (Eucl P) m) (r s : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀ → (∀ (x : Eucl P) (v : Fin m → Eucl P), ψ₀ x v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) → 0 < r → r < s → ∃ ψ : TestFormOn (univ : Set (Eucl P)) m, (∀ x ∈ ball (0 : Eucl P) r, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) ∧ ((∀ y, covectorEuclideanNorm (ω y) ≤ 1) → ∀ x, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl P) m) x) ≤ (P : ℝ) ^ (2 * m + 1) * s)`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.radial_coeff_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
