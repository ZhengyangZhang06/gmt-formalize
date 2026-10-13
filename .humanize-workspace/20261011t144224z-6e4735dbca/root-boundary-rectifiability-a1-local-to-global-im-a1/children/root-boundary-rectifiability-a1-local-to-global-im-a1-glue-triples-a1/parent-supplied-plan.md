# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.local_to_global_im-a1.glue_triples-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-glue-triples-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.local_to_global_im-a1`
- Child key: `glue_triples`
- Declaration: `Submission.ltg_glue_triples`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Eucl P)), (∀ (A A' : Set (Eucl P)) (ϑ ϑ' : Eucl P → ℝ) (x : Eucl P) (W : Set (Eucl P)), IsOpen W → x ∈ W → (μHE[k] : Measure (Eucl P)) (symmDiff A A' ∩ W) = 0 → (∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (A ∩ W)), ϑ y = ϑ' y) → ϑ x = ϑ' x → ∀ L : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k A ϑ x L → HasWeightedApproximateTangentSpaceAt k A' ϑ' x L) → ∀ (V M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (ξ : ℕ → Eucl P → NVector (Eucl P) k), (∀ i, IsOpen (V i)) → U ⊆ ⋃ i, V i → (∀ i, IsRectifiableTriple U k (M i) (θ i) (ξ i)) → (∀ i, ∀ x ∈ M i, ∃ n : ℕ, θ i x = n) → (∀ i j, (μHE[k] : Measure (Eucl P)) (symmDiff (M i) (M j) ∩ (V i ∩ V j)) = 0 ∧ ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ (V i ∩ V j))), θ i x = θ j x ∧ ξ i x = ξ j x) → ∃ (M₀ : Set (Eucl P)) (θ₀ : Eucl P → ℝ) (ξ₀ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M₀ θ₀ ξ₀ ∧ (∀ x ∈ M₀, ∃ n : ℕ, θ₀ x = n) ∧ ∀ i, (μHE[k] : Measure (Eucl P)) (symmDiff (M i) M₀ ∩ V i) = 0 ∧ ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M i ∩ V i)), θ i x = θ₀ x ∧ ξ i x = ξ₀ x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
