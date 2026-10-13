# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1.blowup_domain_eventually-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ef3b26ef10/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_point_tangent_plane-a1`
- Child key: `blowup_domain_eventually`
- Declaration: `Submission.idtp_tpf_blowUp_domain_eventually`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lams : ℕ → ℝ), IsOpen U → x ∈ U → (∀ i, 0 < lams i) → Tendsto lams atTop (𝓝 0) → ∀ K : Set (Euclid P), Bornology.IsBounded K → ∀ᶠ i in atTop, K ⊆ dilation x (lams i) '' U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
