# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1.weak_uniform_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-weak-tendsto-comp-affine-a1-weak-b96b6edd1c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1`
- Child key: `weak_uniform_bound`
- Declaration: `Submission.adr_uniform_bound_of_weak_bounded`
- Exact Lean type: `∀ (P Q : ℕ) (μ : Measure (Euclid P)) (gs : ℕ → Euclid P → Euclid Q) (K : Set (Euclid P)), (∀ k, LocallyIntegrable (gs k) μ) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∃ C, ∀ k, ‖∫ x, f x • gs k x ∂μ‖ ≤ C) → IsCompact K → ∃ M, ∀ (k : ℕ) (h : Euclid P → ℝ) (C : ℝ), Continuous h → (∀ x ∉ K, h x = 0) → (∀ x, |h x| ≤ C) → ‖∫ x, h x • gs k x ∂μ‖ ≤ M * C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
