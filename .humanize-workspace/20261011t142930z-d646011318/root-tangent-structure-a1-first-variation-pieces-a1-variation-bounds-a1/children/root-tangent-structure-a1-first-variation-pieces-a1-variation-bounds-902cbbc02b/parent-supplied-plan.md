# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1.slice_fderiv_time_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-variation-bounds-902cbbc02b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1`
- Child key: `slice_fderiv_time_deriv`
- Declaration: `Submission.ts_fv_cv_slice_fderiv_time_deriv`
- Exact Lean type: `∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ∃ Λ' : ℝ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), (∀ x, Λ' 0 x = fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∧ ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s ↦ fderiv ℝ (φ s) x) (Λ' t x) t) ∧ ∀ δ : ℝ, 0 < δ → δ < ε → ∃ B : ℝ, ∀ x, ∀ t ∈ Ioo (-δ) δ, ‖Λ' t x‖ ≤ B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
