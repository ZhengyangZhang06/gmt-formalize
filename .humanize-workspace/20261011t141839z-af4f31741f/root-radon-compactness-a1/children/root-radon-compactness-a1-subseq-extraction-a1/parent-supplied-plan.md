# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radon_compactness-a1.subseq_extraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-radon-compactness-a1-subseq-extraction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.radon_compactness-a1`
- Child key: `subseq_extraction`
- Declaration: `Submission.radon_exists_subseq_tendsto_integral`
- Exact Lean type: `∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ : ℕ → Measure X), (∀ K : Set X, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᶠ j in atTop, μ j K ≤ C) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : C_c(X, ℝ), ∃ L : ℝ, Tendsto (fun j ↦ ∫ x, f x ∂(μ (φ j))) atTop (𝓝 L)`

## Sibling prerequisites

- `root.radon_compactness-a1.cc_countable_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
