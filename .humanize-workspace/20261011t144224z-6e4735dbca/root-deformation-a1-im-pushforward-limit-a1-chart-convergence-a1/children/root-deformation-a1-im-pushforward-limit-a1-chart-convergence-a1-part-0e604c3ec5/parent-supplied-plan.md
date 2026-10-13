# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.partition_tannery-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-part-0e604c3ec5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child key: `partition_tannery`
- Declaration: `Submission.deformation_ipl_cc_tendsto_setIntegral_of_partition`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (S : Set X) (E : ℕ → Set X) (f : ℕ → X → ℝ) (f₀ G : X → ℝ), (∀ i, NullMeasurableSet (E i) μ) → Pairwise (Function.onFun Disjoint E) → S =ᵐ[μ] (⋃ i, E i) → IntegrableOn G S μ → (∀ j, AEStronglyMeasurable (f j) (μ.restrict S)) → AEStronglyMeasurable f₀ (μ.restrict S) → (∀ᶠ j in atTop, ∀ᵐ x ∂(μ.restrict S), |f j x| ≤ G x) → (∀ᵐ x ∂(μ.restrict S), |f₀ x| ≤ G x) → (∀ i, Tendsto (fun j => ∫ x in E i, f j x ∂μ) atTop (𝓝 (∫ x in E i, f₀ x ∂μ))) → Tendsto (fun j => ∫ x in S, f j x ∂μ) atTop (𝓝 (∫ x in S, f₀ x ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
