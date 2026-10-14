# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.vague_unique-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-98c855726f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child key: `vague_unique`
- Declaration: `Submission.idtp_fons_cc_psf_vague_unique`
- Exact Lean type: `∀ (P : ℕ) (ν₁ ν₂ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → ν₁ K ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → ν₂ K ≠ ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x ∂ν₁ = ∫ x, f x ∂ν₂) → ν₁ = ν₂`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
