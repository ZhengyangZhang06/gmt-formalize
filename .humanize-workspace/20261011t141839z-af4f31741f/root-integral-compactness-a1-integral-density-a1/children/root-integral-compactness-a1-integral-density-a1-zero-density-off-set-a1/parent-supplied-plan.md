# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.integral_density-a1.zero_density_off_set-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-zero-density-off-set-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.integral_density-a1`
- Child key: `zero_density_off_set`
- Declaration: `Submission.intcpt_id_restrict_density_zero_ae`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (U A : Set (Euclidean N)), IsOpen U → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → MeasurableSet A → ∀ᵐ x ∂(μHE[n] : Measure (Euclidean N)), x ∈ U → x ∉ A → HasDensity n (μ.restrict A) x 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
