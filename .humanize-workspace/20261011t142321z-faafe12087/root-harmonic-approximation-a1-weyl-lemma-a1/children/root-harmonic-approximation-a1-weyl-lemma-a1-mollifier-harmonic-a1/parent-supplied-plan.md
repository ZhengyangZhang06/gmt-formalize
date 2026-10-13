# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.weyl_lemma-a1.mollifier_harmonic-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weyl-lemma-a1-mollifier-harmonic-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.weyl_lemma-a1`
- Child key: `mollifier_harmonic`
- Declaration: `Submission.ball_convolution_contDiff_laplacian_eq_zero`
- Exact Lean type: `∀ n : ℕ, 1 ≤ n → ∀ w : Rn n → ℝ, IntegrableOn w (ball (0 : Rn n) 1) → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 → ∫ x in ball (0 : Rn n) 1, w x * Laplacian.laplacian ζ x = 0) → ∀ (κ : Rn n → ℝ) (ε : ℝ), ContDiff ℝ (⊤ : ℕ∞) κ → (∀ z : Rn n, ε ≤ ‖z‖ → κ z = 0) → ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y in ball (0 : Rn n) 1, κ (x - y) * w y) ∧ ∀ x ∈ ball (0 : Rn n) (1 - ε), Laplacian.laplacian (fun x => ∫ y in ball (0 : Rn n) 1, κ (x - y) * w y) x = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
