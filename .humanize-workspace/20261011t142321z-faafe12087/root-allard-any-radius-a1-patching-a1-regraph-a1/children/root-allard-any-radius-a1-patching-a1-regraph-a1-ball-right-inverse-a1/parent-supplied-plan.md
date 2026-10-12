# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.regraph-a1.ball_right_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-regraph-a1-ball-right-inverse-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1.regraph-a1`
- Child key: `ball_right_inverse`
- Declaration: `Submission.arp_rgr_ball_right_inverse`
- Exact Lean type: `∀ {n : ℕ} (Φ : Rn n → Rn n) (A : Rn n →L[ℝ] Rn n) (c : Rn n) (r ε : ℝ), 0 < r → 0 ≤ ε → ε ≤ 1 / 24 → (∀ h : Rn n, 11 / 12 * ‖h‖ ≤ ‖A h‖) → (∀ x₁ ∈ closedBall (0 : Rn n) r, ∀ x₂ ∈ closedBall (0 : Rn n) r, ‖Φ x₁ - Φ x₂ - A (x₁ - x₂)‖ ≤ ε * ‖x₁ - x₂‖) → Φ 0 = c → ∃ X : Rn n → Rn n, (∀ w ∈ closedBall c (r / 2), X w ∈ closedBall (0 : Rn n) (3 * r / 5) ∧ Φ (X w) = w) ∧ (∀ x ∈ closedBall (0 : Rn n) r, ∀ w ∈ closedBall c (r / 2), Φ x = w → x = X w) ∧ (∀ w₁ ∈ closedBall c (r / 2), ∀ w₂ ∈ closedBall c (r / 2), 7 / 8 * ‖X w₁ - X w₂‖ ≤ ‖w₁ - w₂‖)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
