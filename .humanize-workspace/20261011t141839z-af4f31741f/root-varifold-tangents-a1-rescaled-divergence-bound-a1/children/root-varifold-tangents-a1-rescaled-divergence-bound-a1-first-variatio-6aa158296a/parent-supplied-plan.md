# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.rescaled_divergence_bound-a1.first_variation_sup_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-rescaled-divergence-bound-a1-first-variatio-6aa158296a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.rescaled_divergence_bound-a1`
- Child key: `first_variation_sup_bound`
- Declaration: `Submission.varifold_tangents_rdb_firstVariation_le_variationMeasure`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (W : Set (Euclidean N)) (Y : Euclidean N → Euclidean N) (K : ℝ), V.HasLocallyBoundedFirstVariation → IsOpen W → IsCompact (closure W) → closure W ⊆ U → ContDiff ℝ 1 Y → tsupport Y ⊆ W → (∀ z, ‖Y z‖ ≤ K) → ENNReal.ofReal |V.firstVariation Y| ≤ ENNReal.ofReal K * variationMeasure V W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
