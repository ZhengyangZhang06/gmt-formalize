# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.antipodal-a1.chord-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-bc9dda22f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.antipodal-a1`
- Child key: `chord`
- Declaration: `Submission.idtp_fons_odc_antipodal_chord`
- Exact Lean type: `∀ (P : ℕ) (a b : Euclid P), ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b → b ≠ -a → ∃ (ℓ : ℝ) (u : Euclid P), 0 < ℓ ∧ ‖a - b‖ = ℓ ∧ ‖u‖ = 1 ∧ b + ℓ • u = a ∧ (∀ s ∈ Icc (0 : ℝ) ℓ, ‖b + s • u‖ ≤ 1) ∧ ∀ (e : Euclid P) (s₁ s₂ t₁ t₂ : ℝ), b + s₁ • u = t₁ • e → b + s₂ • u = t₂ • e → s₁ = s₂`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
