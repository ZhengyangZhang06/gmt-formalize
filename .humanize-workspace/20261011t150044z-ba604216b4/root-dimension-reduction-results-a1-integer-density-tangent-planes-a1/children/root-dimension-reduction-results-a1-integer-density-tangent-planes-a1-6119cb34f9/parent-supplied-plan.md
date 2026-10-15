# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.density_eq_multiplicity_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-6119cb34f9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child key: `density_eq_multiplicity_ae`
- Declaration: `Submission.idtp_imrep_measure_density_ae`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), 1 ≤ n → (∀ K : Set (Euclid P), IsCompact K → R.measure K ≠ ∞) → ∀ᵐ x ∂μHE[n], Tendsto (fun ρ : ℝ => R.measure (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (Set.indicator R.carrier (fun y => (R.mult y : ℝ≥0∞)) x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
