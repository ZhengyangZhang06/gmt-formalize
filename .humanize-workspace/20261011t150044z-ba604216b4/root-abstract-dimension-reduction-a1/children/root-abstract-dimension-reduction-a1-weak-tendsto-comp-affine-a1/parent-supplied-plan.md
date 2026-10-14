# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-weak-tendsto-comp-affine-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1`
- Child key: `weak_tendsto_comp_affine`
- Declaration: `Submission.adr_weak_tendsto_comp_affine`
- Exact Lean type: `∀ (P n Q : ℕ) (gs : ℕ → Euclid P → Euclid Q) (g : Euclid P → Euclid Q) (y : Euclid P) (mus : ℕ → ℝ), (∀ k, LocallyIntegrable (gs k) μH[(n : ℝ)]) → (∀ k, 0 < mus k) → Tendsto mus atTop (𝓝 1) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • g x ∂μH[(n : ℝ)]))) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k (y + mus k • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • g (y + x) ∂μH[(n : ℝ)]))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
