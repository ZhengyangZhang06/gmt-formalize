# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.homogeneous_infinite_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-measure-cl-4fc3ef1ab3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1`
- Child key: `homogeneous_infinite_mass`
- Declaration: `Submission.dimred_tr_mcr_homogeneous_infinite_mass`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (x₀ : Euclid P), 1 ≤ n → (∀ x, g x = (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) → μ = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal (g x)) → (∀ t : ℝ, 0 < t → ∀ x, g (t • x) = g x) → 0 < g x₀ → μ univ = ∞`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.nonhomogeneous-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
