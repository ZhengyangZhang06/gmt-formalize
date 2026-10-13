# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.lipschitz_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-3c55029282/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child key: `lipschitz_graph`
- Declaration: `Submission.codim1_rdo_dg_rc_closed_graph_cover`
- Exact Lean type: `∀ (m : ℕ) (v : Euclid (m + 1)) (S : Set (Euclid (m + 1))), ‖v‖ = 1 → (∀ x ∈ S, ∀ x' ∈ S, |inner ℝ (x' - x) v| ≤ ‖x' - x‖ / 2) → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ S ⊆ Γ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
