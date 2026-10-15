# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.density_normalization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-644d8df7fd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`
- Child key: `density_normalization`
- Declaration: `Submission.idtp_fons_cr_density_normalization`
- Exact Lean type: `∀ (P n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (Q : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (e : Euclid Q), Measurable g → (∀ x, 0 ≤ g x) → (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → μ = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal (g x)) → LocallyIntegrable (fun x => g x • e) μH[(n : ℝ)] ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x • (g x • e) ∂μH[(n : ℝ)] = (c * ∫ x, f x ∂μ) • e`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
