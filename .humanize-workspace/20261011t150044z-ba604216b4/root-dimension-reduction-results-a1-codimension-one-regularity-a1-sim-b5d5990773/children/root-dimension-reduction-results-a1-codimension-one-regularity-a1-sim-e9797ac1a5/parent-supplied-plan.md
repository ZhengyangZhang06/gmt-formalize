# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e9797ac1a5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1`
- Child key: `lipschitz_approx`
- Declaration: `Submission.codim1_hcp_lipschitz_smooth_approx`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → (∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → ∀ j : Fin P, AEStronglyMeasurable (fun x => fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M)) ∧ ∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧ C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧ (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs ζ atTop M ∧ Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) - fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0)`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`
- `root.dimension_reduction_results-a1.regular_point_density-a1.locally_closed-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
