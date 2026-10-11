# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.weak_compactness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-weak-compactness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1`
- Child key: `weak_compactness`
- Declaration: `Submission.l2_ball_weak_subsequence`
- Exact Lean type: `∀ (n : ℕ) (G : ℕ → Rn n → Rn n), (∀ k, MemLp (G k) 2 (volume.restrict (ball (0 : Rn n) 1))) → (∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖G k x‖ₑ ^ 2 ≤ 1) → ∃ (φ : ℕ → ℕ) (g : Rn n → Rn n), StrictMono φ ∧ MemLp g 2 (volume.restrict (ball (0 : Rn n) 1)) ∧ ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 ≤ 1 ∧ ∀ h : Rn n → Rn n, MemLp h 2 (volume.restrict (ball (0 : Rn n) 1)) → Tendsto (fun k => ∫ x in ball (0 : Rn n) 1, inner ℝ (G (φ k) x) (h x)) atTop (𝓝 (∫ x in ball (0 : Rn n) 1, inner ℝ (g x) (h x)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
