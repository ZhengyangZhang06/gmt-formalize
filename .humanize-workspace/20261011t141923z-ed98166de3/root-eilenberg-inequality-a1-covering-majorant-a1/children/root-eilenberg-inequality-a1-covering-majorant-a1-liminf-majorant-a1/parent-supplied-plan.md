# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.eilenberg_inequality-a1.covering_majorant-a1.liminf_majorant-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-eilenberg-inequality-a1-covering-majorant-a1-liminf-majorant-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.eilenberg_inequality-a1.covering_majorant-a1`
- Child key: `liminf_majorant`
- Declaration: `Submission.eilenberg_covering_liminf_majorant`
- Exact Lean type: `∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (d : ℝ) (c : ℝ≥0∞) (F : Y → Set X) (r : ℕ → ℝ≥0∞) (g : ℕ → Y → ℝ≥0∞) (b : ℕ → ℝ≥0∞) (L : ℝ≥0∞), Tendsto r atTop (𝓝 0) → (∀ i, Measurable (g i)) → (∀ (i : ℕ) (y : Y), c * (⨅ (t : ℕ → Set X) (_ : F y ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r i), ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ d) ≤ g i y) → (∀ i, ∫⁻ y, g i y ∂ν ≤ b i) → Tendsto b atTop (𝓝 L) → ∃ G : Y → ℝ≥0∞, Measurable G ∧ (∀ y, c * μH[d] (F y) ≤ G y) ∧ ∫⁻ y, G y ∂ν ≤ L`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
