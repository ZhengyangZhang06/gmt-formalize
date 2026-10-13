# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1.affine_combine-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-cluster-bound-a-f011c8ede8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_cluster_bound-a1`
- Child key: `affine_combine`
- Declaration: `Submission.intcpt_allard_ccb_affine_combine`
- Exact Lean type: `∀ (b c c' k δ : ℝ) (X Y M : ℝ≥0∞), 0 ≤ b → 0 ≤ c → 0 ≤ k → δ ^ 2 ≤ 1 → b + c + b * c ≤ c' → (1 + b) * c + k ≤ c' → X ≤ ENNReal.ofReal (1 + b * δ ^ 2) * Y + ENNReal.ofReal (k * δ ^ 2) → Y ≤ ENNReal.ofReal (1 + c * δ ^ 2) * M + ENNReal.ofReal (c * δ ^ 2) → X ≤ ENNReal.ofReal (1 + c' * δ ^ 2) * M + ENNReal.ofReal (c' * δ ^ 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
