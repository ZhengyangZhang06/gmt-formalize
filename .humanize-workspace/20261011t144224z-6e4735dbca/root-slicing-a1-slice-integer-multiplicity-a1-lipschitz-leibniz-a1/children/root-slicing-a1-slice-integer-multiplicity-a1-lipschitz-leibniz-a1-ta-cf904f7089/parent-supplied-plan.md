# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-cf904f7089/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1`
- Child key: `tangential_weak_limit`
- Declaration: `Submission.slicing_im_ll_tangential_weak_limit`
- Exact Lean type: `∀ (P n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsOpen U → IsRectifiableTriple U n M θ ξ → ∀ (h : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), LipschitzWith L h → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => h (x + s • u)) (inner ℝ (G x) u) 0) → ∀ Y : Eucl P → Eucl P, Integrable Y ((μHE[n] : Measure (Eucl P)).restrict M) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q → Y x ∈ Q) → ∀ g : ℕ → Eucl P → ℝ, (∀ k, Differentiable ℝ (g k)) → (∀ k, LipschitzWith L (g k)) → TendstoUniformly g h atTop → Tendsto (fun k => ∫ x in M, fderiv ℝ (g k) x (Y x) ∂(μHE[n] : Measure (Eucl P))) atTop (𝓝 (∫ x in M, inner ℝ (G x) (Y x) ∂(μHE[n] : Measure (Eucl P))))`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
