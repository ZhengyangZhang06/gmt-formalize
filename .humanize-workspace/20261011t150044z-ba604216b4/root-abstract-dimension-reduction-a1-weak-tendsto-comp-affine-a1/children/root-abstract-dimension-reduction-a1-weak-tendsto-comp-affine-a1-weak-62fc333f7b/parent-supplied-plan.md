# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1.weak_tendsto_moving_tests-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-weak-tendsto-comp-affine-a1-weak-62fc333f7b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1`
- Child key: `weak_tendsto_moving_tests`
- Declaration: `Submission.adr_weak_tendsto_of_tendstoUniformly`
- Exact Lean type: `∀ (P Q : ℕ) (μ : Measure (Euclid P)) (gs : ℕ → Euclid P → Euclid Q) (g : Euclid P → Euclid Q) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (K : Set (Euclid P)), (∀ k, LocallyIntegrable (gs k) μ) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k x ∂μ) atTop (𝓝 (∫ x, f x • g x ∂μ))) → IsCompact K → (∀ k, Continuous (hs k)) → Continuous h → (∀ᶠ k in atTop, ∀ x ∉ K, hs k x = 0) → (∀ x ∉ K, h x = 0) → TendstoUniformly hs h atTop → Tendsto (fun k => ∫ x, hs k x • gs k x ∂μ) atTop (𝓝 (∫ x, h x • g x ∂μ))`

## Sibling prerequisites

- `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1.weak_uniform_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
