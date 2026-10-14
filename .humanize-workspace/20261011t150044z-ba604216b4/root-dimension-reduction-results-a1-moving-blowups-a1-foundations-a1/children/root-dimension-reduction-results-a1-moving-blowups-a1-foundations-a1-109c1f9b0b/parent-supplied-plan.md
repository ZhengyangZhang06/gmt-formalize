# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.coordinate_covectors-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-foundations-a1-109c1f9b0b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1`
- Child key: `coordinate_covectors`
- Declaration: `Submission.dimred_mbl_fnd_coordinate_covectors_span`
- Exact Lean type: `∀ (P n : ℕ), (∀ I : Fin n → Fin P, ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) ∧ ∀ ζ : MultiVector P n, (∀ (I : Fin n → Fin P) (θ : Covector (Euclid P) n), StrictMono I → (∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → ζ θ = 0) → ζ = 0`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.covector_euclidean_equiv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
