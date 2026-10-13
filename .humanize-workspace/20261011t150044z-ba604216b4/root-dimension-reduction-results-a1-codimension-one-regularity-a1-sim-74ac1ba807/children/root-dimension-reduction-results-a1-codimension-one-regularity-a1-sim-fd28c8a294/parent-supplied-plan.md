# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.energy_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-fd28c8a294/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child key: `energy_convergence`
- Declaration: `Submission.codim1_hcp_stab_energy_convergence`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (F : ℕ → Fin P → Euclid P → ℝ) (G : Fin P → Euclid P → ℝ), (∀ k j, AEStronglyMeasurable (F k j) μ) → (∀ j, AEStronglyMeasurable (G j) μ) → (∀ k, Integrable (fun x => ∑ j : Fin P, (F k j x) ^ 2) μ) → Tendsto (fun k => ∫⁻ x, ENNReal.ofReal (∑ j : Fin P, (F k j x - G j x) ^ 2) ∂μ) atTop (𝓝 0) → Integrable (fun x => ∑ j : Fin P, (G j x) ^ 2) μ ∧ Tendsto (fun k => ∫ x, ∑ j : Fin P, (F k j x) ^ 2 ∂μ) atTop (𝓝 (∫ x, ∑ j : Fin P, (G j x) ^ 2 ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
