# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radon_compactness-a1.rc_subseq_integrals_converge-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/nodes/root-radon-compactness-a1-rc-subseq-integrals-converge-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.radon_compactness-a1`
- Child key: `rc_subseq_integrals_converge`
- Declaration: `Submission.rc_subseq_integrals_converge`
- Exact Lean type: `∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] (μ : ℕ → OuterMeasure X), (∀ k, IsRadonOuterMeasure (μ k)) → (∀ K : Set X, IsCompact K → ⨆ k, μ k K < ∞) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : C_c(X, ℝ), ∃ l : ℝ, Tendsto (fun k => ∫ x, f x ∂caratheodoryMeasure (μ (φ k))) atTop (𝓝 l)`

## Sibling prerequisites

- `root.radon_compactness-a1.rc_cc_integrable-a1`
- `root.radon_compactness-a1.rc_cc_integral_abs_le-a1`
- `root.radon_compactness-a1.rc_diagonal_subseq-a1`
- `root.radon_compactness-a1.rc_cc_countable_dense-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
