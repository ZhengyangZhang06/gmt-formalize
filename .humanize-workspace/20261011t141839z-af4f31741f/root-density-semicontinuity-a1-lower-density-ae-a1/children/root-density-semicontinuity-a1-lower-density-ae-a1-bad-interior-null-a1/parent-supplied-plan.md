# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.lower_density_ae-a1.bad_interior_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-lower-density-ae-a1-bad-interior-null-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1.lower_density_ae-a1`
- Child key: `bad_interior_null`
- Declaration: `Submission.measure_bad_interior_exceptional_eq_zero`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)) (μs : ℕ → Measure (Euclidean N)) (W : Set (Euclidean N)) (Bad : ℕ → ℕ → Set (Euclidean N)) (C : ℕ) (a b : ℕ → ℝ≥0∞), (∀ O : Set (Euclidean N), IsOpen O → O ⊆ W → μ O ≤ liminf (fun q ↦ μs q O) atTop) → (∀ q k, Bad q k ⊆ W) → liminf a atTop ≠ ∞ → Tendsto b atTop (𝓝 0) → (∀ q k : ℕ, 1 ≤ k → μs q (Bad q k) ≤ (C : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ * a q + b q) → μ (⋂ k : ℕ, ⋂ (_ : 1 ≤ k), ⋃ i : ℕ, interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ k)) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
