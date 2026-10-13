# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.radial_coeff_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1-cde2281771/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1`
- Child key: `radial_coeff_bound`
- Declaration: `Submission.iwl_cr_cest_radial_coeff_bound`
- Exact Lean type: `∀ (P m : ℕ) (ω : DifferentialForm (Eucl P) (m + 1)) (x : Eucl P) (β : Covector (Eucl P) m), (∀ y, covectorEuclideanNorm (ω y) ≤ 1) → (∀ v : Fin m → Eucl P, β v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) → covectorEuclideanNorm β ≤ (P : ℝ) ^ (2 * m + 1) * ‖x‖`

## Sibling prerequisites

- `root.isoperimetric-a1.covector_eval_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
