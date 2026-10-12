# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.first_variation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-first-variation-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1`
- Child key: `first_variation_bound`
- Declaration: `Submission.intcpt_allard_first_variation_le_sup_mul`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (X : Euclidean N → Euclidean N) (K : Set (Euclidean N)) (B : ℝ), W.HasLocallyBoundedFirstVariation → ContDiff ℝ 1 X → IsCompact K → K ⊆ U → tsupport X ⊆ K → (∀ z, ‖X z‖ ≤ B) → ENNReal.ofReal |W.firstVariation X| ≤ ENNReal.ofReal B * variationMeasure W K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
