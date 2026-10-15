# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.density_rescale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3a383ffd93/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`
- Child key: `density_rescale`
- Declaration: `Submission.idtp_fons_cr_density_rescale`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (t : ℝ), 0 < t → (∀ w : Euclid P, limsup (fun ρ : ℝ => (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t)) (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) = limsup (fun ρ : ℝ => μ (ball (y + t • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)) ∧ ∀ w : Euclid P, (∀ ε : ℝ, 0 < ε → (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t)) (ball w ε) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → μ (ball (y + t • w) ε) ≠ 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
