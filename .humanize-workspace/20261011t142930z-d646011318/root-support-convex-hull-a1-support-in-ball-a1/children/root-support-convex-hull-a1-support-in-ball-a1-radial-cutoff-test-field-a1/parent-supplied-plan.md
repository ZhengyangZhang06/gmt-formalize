# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.support_convex_hull-a1.support_in_ball-a1.radial_cutoff_test_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-support-convex-hull-a1-support-in-ball-a1-radial-cutoff-test-field-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.support_convex_hull-a1.support_in_ball-a1`
- Child key: `radial_cutoff_test_field`
- Declaration: `Submission.exists_radial_cutoff_test_field`
- Exact Lean type: `∀ (n ℓ : ℕ) (K : Set (Ambient n ℓ)) (ξ : Ambient n ℓ) (R ε : ℝ), IsCompact K → 0 ≤ R → 0 < ε → ∃ (ζ : Ambient n ℓ → ℝ) (γ : ℝ → ℝ), ContDiff ℝ 1 ζ ∧ (∀ x ∈ K, ζ x = 1 ∧ gradient ζ x = 0) ∧ ContDiff ℝ 1 γ ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ γ t ∧ 0 ≤ deriv γ t) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ R + ε → γ t = 0) ∧ (∀ t : ℝ, R + ε < t → 0 < γ t) ∧ IsTestField (closedBall ξ R)ᶜ (fun x ↦ (ζ x * γ ‖x - ξ‖) • (x - ξ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
