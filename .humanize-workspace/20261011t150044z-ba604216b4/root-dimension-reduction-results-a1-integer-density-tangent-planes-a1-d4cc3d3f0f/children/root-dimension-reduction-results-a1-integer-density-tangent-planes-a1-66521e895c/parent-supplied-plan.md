# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.nonhomogeneous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-66521e895c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child key: `nonhomogeneous`
- Declaration: `Submission.idtp_fons_cc_psf_nonhomogeneous`
- Exact Lean type: `∀ (P n : ℕ) (ν : Measure (Euclid P)) (f : Euclid P → ℝ≥0∞), 1 ≤ n → ν univ ≠ 0 → ν univ ≠ ∞ → (∀ t : ℝ, 0 < t → ∀ w : Euclid P, f (t • w) = f w) → ν ≠ (μHE[n] : Measure (Euclid P)).withDensity f`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1.dilate_homogeneity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
