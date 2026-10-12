# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.radial_test_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-radial-test-field-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1`
- Child key: `radial_test_field`
- Declaration: `Submission.weighted_mono_radial_test_field`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Ambient n ℓ)) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ) (a b : ℝ), IsOpen U → ContDiffOn ℝ 1 h U → ContDiff ℝ 1 γ → 0 < a → (∀ t, t ≤ a → γ t = γ 0) → (∀ t, b ≤ t → γ t = 0) → tsupport h ∩ closedBall ξ b ⊆ U → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
