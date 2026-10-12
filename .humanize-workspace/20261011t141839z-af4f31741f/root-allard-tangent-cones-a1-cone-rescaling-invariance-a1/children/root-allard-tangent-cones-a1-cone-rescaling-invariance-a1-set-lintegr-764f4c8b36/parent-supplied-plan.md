# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.set_lintegral_congr_off_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-cone-rescaling-invariance-a1-set-lintegr-764f4c8b36/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1`
- Child key: `set_lintegral_congr_off_null`
- Declaration: `Submission.allard_tc_cri_setLIntegral_congr_off_null`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)) (G D D' : Set (Euclidean N)) (f g : Euclidean N → ℝ≥0∞), NullMeasurableSet G μ → μ (D \ G) = 0 → μ (D' \ G) = 0 → (∀ x ∈ G, x ∈ D ↔ x ∈ D') → (∀ x ∈ G, f x = g x) → ∫⁻ x in D, f x ∂μ = ∫⁻ x in D', g x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
