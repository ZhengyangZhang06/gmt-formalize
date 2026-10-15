# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.tangent_measures-a1.density_homogeneous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5a68c13034/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.tangent_measures-a1`
- Child key: `density_homogeneous`
- Declaration: `Submission.idtp_fons_cc_tm_density_homogeneous`
- Exact Lean type: `∀ (P n : ℕ) (ν : Measure (Euclid P)), (∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * ν A) → ∀ t : ℝ, 0 < t → ∀ w : Euclid P, limsup (fun ρ : ℝ => ν (ball (t • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) = limsup (fun ρ : ℝ => ν (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
