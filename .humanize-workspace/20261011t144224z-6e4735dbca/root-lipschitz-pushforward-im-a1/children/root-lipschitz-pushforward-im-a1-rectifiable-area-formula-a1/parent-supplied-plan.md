# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1`
- Child key: `rectifiable_area_formula`
- Declaration: `Submission.lpf_rectifiable_area_formula`
- Exact Lean type: `∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → AEStronglyMeasurable L ((μHE[n] : Measure (Eucl P)).restrict M) → ∀ (A : Set (Eucl P)) (h : Eucl P → ℝ≥0∞), A ⊆ M → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → AEMeasurable h ((μHE[n] : Measure (Eucl P)).restrict A) → AEMeasurable (fun y => ∑' x : {x : Eucl P // x ∈ A ∧ f x = y}, h x) (μHE[n] : Measure (Eucl Q)) ∧ ∫⁻ x in A, h x * ‖nVectorPushforward n (L x) (ξ x)‖ₑ ∂(μHE[n] : Measure (Eucl P)) = ∫⁻ y, ∑' x : {x : Eucl P // x ∈ A ∧ f x = y}, h x ∂(μHE[n] : Measure (Eucl Q))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.simple_nvector_algebra-a1`
- `root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1`
- `root.lipschitz_pushforward_im-a1.countably_rectifiable_c1_cover-a1`
- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
