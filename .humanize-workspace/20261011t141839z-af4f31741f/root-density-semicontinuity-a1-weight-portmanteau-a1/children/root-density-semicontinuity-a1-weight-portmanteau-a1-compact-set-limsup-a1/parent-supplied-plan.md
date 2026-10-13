# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.weight_portmanteau-a1.compact_set_limsup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-weight-portmanteau-a1-compact-set-limsup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1.weight_portmanteau-a1`
- Child key: `compact_set_limsup`
- Declaration: `Submission.limsup_measure_compact_le_of_tendsto_integral`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Euclidean N)) (μs : ℕ → Measure (Euclidean N)) (μ : Measure (Euclidean N)), IsOpen U → (∀ (i : ℕ) (K : Set (Euclidean N)), IsCompact K → K ⊆ U → μs i K ≠ ∞) → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → μ K ≠ ∞) → (∀ g : Euclidean N → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Tendsto (fun i ↦ ∫ x, g x ∂(μs i)) atTop (𝓝 (∫ x, g x ∂μ))) → ∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → limsup (fun i ↦ μs i K) atTop ≤ μ K`

## Sibling prerequisites

- `root.density_semicontinuity-a1.weight_portmanteau-a1.urysohn_sandwich-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
