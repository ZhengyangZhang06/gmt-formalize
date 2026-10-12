# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1.rescaled_translate_converge-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-weak-tendsto-comp-affine-a1-resc-03a6c5b658/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1`
- Child key: `rescaled_translate_converge`
- Declaration: `Submission.adr_rescaled_translate_tendstoUniformly`
- Exact Lean type: `∀ (P : ℕ) (f : Euclid P → ℝ) (y : Euclid P) (mus : ℕ → ℝ), Continuous f → HasCompactSupport f → Tendsto mus atTop (𝓝 1) → ∃ K : Set (Euclid P), IsCompact K ∧ (∀ w ∉ K, f (w - y) = 0) ∧ (∀ᶠ k in atTop, ∀ w ∉ K, f ((mus k)⁻¹ • (w - y)) = 0) ∧ TendstoUniformly (fun k w => f ((mus k)⁻¹ • (w - y))) (fun w => f (w - y)) atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
