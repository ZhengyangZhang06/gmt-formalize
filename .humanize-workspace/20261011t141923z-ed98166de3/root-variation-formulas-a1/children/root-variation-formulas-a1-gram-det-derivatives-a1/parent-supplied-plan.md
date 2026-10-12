# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.gram_det_derivatives-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-gram-det-derivatives-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1`
- Child key: `gram_det_derivatives`
- Declaration: `Submission.variation_gram_det_derivatives`
- Exact Lean type: `∀ (N : ℕ) (T : Submodule ℝ (Rn N)) (ι : Type) [Fintype ι] (b : OrthonormalBasis ι ℝ T) (A : ℝ → Rn N →L[ℝ] Rn N), A 0 = 1 → let j : ℝ → ℝ := fun t ↦ Real.sqrt ((1 - T.starProjection + T.starProjection ∘L ContinuousLinearMap.adjoint (A t) ∘L A t ∘L T.starProjection).det); (∀ A₁ : Rn N →L[ℝ] Rn N, HasDerivAt A A₁ 0 → HasDerivAt j (∑ i, inner ℝ (b i : Rn N) (A₁ (b i : Rn N))) 0) ∧ ∀ A₁ A₂ : Rn N →L[ℝ] Rn N, (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ A t) → HasDerivAt A A₁ 0 → HasDerivAt (deriv A) A₂ 0 → HasDerivAt (deriv j) (∑ i, inner ℝ (b i : Rn N) (A₂ (b i : Rn N)) + (∑ i, inner ℝ (b i : Rn N) (A₁ (b i : Rn N))) ^ 2 + ∑ i, ‖A₁ (b i : Rn N) - T.starProjection (A₁ (b i : Rn N))‖ ^ 2 - ∑ i, ∑ k, inner ℝ (b i : Rn N) (A₁ (b k : Rn N)) * inner ℝ (b k : Rn N) (A₁ (b i : Rn N))) 0`

## Sibling prerequisites

- `root.variation_formulas-a1.gram_det_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
