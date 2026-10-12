# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.c1_piece_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1-c1-piece-tangent-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1`
- Child key: `c1_piece_tangent`
- Declaration: `Submission.aetp_c1_piece_approxTangent`
- Exact Lean type: `∀ (n ℓ : ℕ) (G : Rn n → Amb n ℓ) (c : Rn n) (r σ : ℝ), ContDiff ℝ 1 G → 0 < σ → (∀ b ∈ ball c r, Function.Injective (fderiv ℝ G b)) → (∀ b₁ ∈ ball c r, ∀ b₂ ∈ ball c r, σ * ‖b₁ - b₂‖ ≤ ‖G b₁ - G b₂‖) → MeasurableSet (G '' ball c r) ∧ (μHE[n] : Measure (Amb n ℓ)) (G '' ball c r) < ⊤ ∧ ∀ b ∈ ball c r, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (G '' ball c r) (G b) (LinearMap.range (fderiv ℝ G b).toLinearMap)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
