# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.null_slices-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-null-slices-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1`
- Child key: `null_slices`
- Declaration: `Submission.coarea_null_slices_of_eilenberg`
- Exact Lean type: `(∀ (N m k : ℕ), ∃ C : ℝ≥0, ∀ (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μHE[k] (A ∩ f ⁻¹' {y}) ≤ g y) ∧ ∫⁻ y, g y ≤ ((C * L ^ m : ℝ≥0) : ℝ≥0∞) * μHE[m + k] A) → ∀ (N m k : ℕ) (U Z : Set (Rn N)) (f : Rn N → Rn m), LocallyLipschitzOn U f → Z ⊆ U → μHE[m + k] Z = 0 → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (Z ∩ f ⁻¹' {y}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
