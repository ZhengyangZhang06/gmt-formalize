# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1`
- Child key: `chart_convergence`
- Declaration: `Submission.deformation_ipl_chart_convergence`
- Exact Lean type: `∀ (P Q k : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (g : Eucl P → Eucl Q) (Λ : ℝ≥0) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsRectifiableTriple (univ : Set (Eucl P)) k M θ ξ → LipschitzWith Λ g → (∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => g (x + t • v)) (L x v) 0) → (∀ K : Set (Eucl Q), IsCompact K → IntegrableOn θ (M ∩ g ⁻¹' K) (μHE[k] : Measure (Eucl P))) → ∀ (gj : ℕ → Eucl P → Eucl Q) (Λ' : ℝ≥0), (∀ j, ContDiff ℝ 1 (gj j)) → (∀ j, LipschitzWith Λ' (gj j)) → TendstoUniformly gj g atTop → ∀ ω : Eucl Q → Covector (Eucl Q) k, Continuous ω → HasCompactSupport ω → Tendsto (fun j => ∫ x in M, θ x * nVectorPushforward k (fderiv ℝ (gj j) x) (ξ x) (ω (gj j x)) ∂(μHE[k] : Measure (Eucl P))) atTop (𝓝 (∫ x in M, θ x * nVectorPushforward k (L x) (ξ x) (ω (g x)) ∂(μHE[k] : Measure (Eucl P))))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.simple_nvector_algebra-a1`
- `root.lipschitz_pushforward_im-a1.countably_rectifiable_c1_cover-a1`
- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1`
- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1`
- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- `root.deformation-a1.im_pushforward_limit-a1.pushforward_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
