# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.canonical_representation-a1.null_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1-null-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.canonical_representation-a1`
- Child key: `null_transfer`
- Declaration: `Submission.intcpt_canon_hausdorff_null_of_weight_null`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (U Z : Set (Euclidean N)), IsOpen U → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → Z ⊆ U → μ Z = 0 → (∀ x ∈ Z, 0 < limsup (densityRatio n μ x) (𝓝[>] 0)) → (μHE[n] : Measure (Euclidean N)) Z = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
