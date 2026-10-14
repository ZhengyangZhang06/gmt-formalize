# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.monotonicity_bounds-a1.mass_dichotomy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-407ac2f724/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.monotonicity_bounds-a1`
- Child key: `mass_dichotomy`
- Declaration: `Submission.idtp_fons_cc_mb_mass_dichotomy`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)), 1 ≤ n → (∀ w : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball w ε) ≠ 0) → ∀ ρ : ℝ, 0 < ρ → unitBallVolume n * ENNReal.ofReal (ρ ^ n) ≤ μ (ball w ρ)) → μ univ = 0 ∨ μ univ = ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
