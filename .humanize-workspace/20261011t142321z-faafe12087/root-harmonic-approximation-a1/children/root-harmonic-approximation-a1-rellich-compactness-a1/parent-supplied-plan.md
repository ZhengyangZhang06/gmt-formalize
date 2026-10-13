# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.rellich_compactness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-rellich-compactness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1`
- Child key: `rellich_compactness`
- Declaration: `Submission.w12_ball_rellich_compactness`
- Exact Lean type: `∀ n : ℕ, 1 ≤ n → ∀ (A : ℝ) (f : ℕ → Rn n → ℝ) (g : ℕ → Rn n → Rn n), (∀ k, IsW12WithGradient (f k) (g k) (ball 0 1)) → (∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖f k x‖ₑ ^ 2 ≤ ENNReal.ofReal A) → (∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖g k x‖ₑ ^ 2 ≤ ENNReal.ofReal A) → ∃ (φ : ℕ → ℕ) (w : Rn n → ℝ), StrictMono φ ∧ MemLp w 2 (volume.restrict (ball (0 : Rn n) 1)) ∧ Tendsto (fun k => ∫⁻ x in ball (0 : Rn n) 1, ‖f (φ k) x - w x‖ₑ ^ 2) atTop (𝓝 0)`

## Sibling prerequisites

- `root.harmonic_approximation-a1.boundary_layer_estimate-a1`
- `root.harmonic_approximation-a1.translation_estimate-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
