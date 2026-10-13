# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.c1_piece_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1-c1-piece-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1`
- Child key: `c1_piece_cover`
- Declaration: `Submission.aetp_rectifiable_c1_piece_cover`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (M : Set (Amb n ℓ)), Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ Z₀ : Set (Amb n ℓ), MeasurableSet Z₀ ∧ (μHE[n] : Measure (Amb n ℓ)) Z₀ = 0 ∧ ∃ (G : ℕ → Rn n → Amb n ℓ) (c : ℕ → Rn n) (r σ : ℕ → ℝ), (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, 0 < r k) ∧ (∀ k, 0 < σ k) ∧ (∀ k, ∀ b ∈ ball (c k) (r k), Function.Injective (fderiv ℝ (G k) b)) ∧ (∀ k, ∀ b₁ ∈ ball (c k) (r k), ∀ b₂ ∈ ball (c k) (r k), σ k * ‖b₁ - b₂‖ ≤ ‖G k b₁ - G k b₂‖) ∧ M ⊆ Z₀ ∪ ⋃ k, G k '' ball (c k) (r k)`

## Sibling prerequisites

- `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.c1_approximation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
