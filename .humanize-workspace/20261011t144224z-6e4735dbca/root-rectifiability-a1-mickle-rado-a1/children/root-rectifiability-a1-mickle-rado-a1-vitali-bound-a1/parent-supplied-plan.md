# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.mickle_rado-a1.vitali_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1-vitali-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.mickle_rado-a1`
- Child key: `vitali_bound`
- Declaration: `Submission.rectifiability_mickle_rado_vitali_bound`
- Exact Lean type: `∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (K : Set (Eucl (m + 1))) (C : ℝ≥0∞) (r : ℝ), IsClosed K → ψ K = 0 → (∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) r, ψ (ball z τ) ≤ C * ENNReal.ofReal (τ ^ (m + 1))) → ∀ c₀ ∈ K, ∀ t : ℝ, 0 < t → 6 * t ≤ r → ψ (ball c₀ t) * (volume : Measure (Eucl (m + 1))) (ball 0 1) ≤ C * 6 ^ (m + 1) * (volume : Measure (Eucl (m + 1))) (ball c₀ (2 * t) \ K)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
