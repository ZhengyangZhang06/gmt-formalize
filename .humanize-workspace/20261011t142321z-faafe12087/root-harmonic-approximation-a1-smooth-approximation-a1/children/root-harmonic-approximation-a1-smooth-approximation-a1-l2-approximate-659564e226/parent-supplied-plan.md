# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.smooth_approximation-a1.l2_approximate_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-smooth-approximation-a1-l2-approximate-659564e226/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.smooth_approximation-a1`
- Child key: `l2_approximate_identity`
- Declaration: `Submission.mollifier_l2_tendsto`
- Exact Lean type: `∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (H : Rn n → E), Integrable H → MemLp H 2 volume → ∀ (ρ : ℕ → Rn n → ℝ) (ε : ℕ → ℝ), (∀ j, Continuous (ρ j)) → (∀ j z, 0 ≤ ρ j z) → (∀ j, ∫ z, ρ j z = 1) → (∀ j z, ε j ≤ ‖z‖ → ρ j z = 0) → Tendsto ε atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x, ‖(∫ z, ρ j z • H (x - z)) - H x‖ₑ ^ 2) atTop (𝓝 0)`

## Sibling prerequisites

- `root.harmonic_approximation-a1.smooth_approximation-a1.l2_contraction-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
