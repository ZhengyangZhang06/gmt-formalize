# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.weighted_lebesgue_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1-weigh-b112046287/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1`
- Child key: `weighted_lebesgue_point`
- Declaration: `Submission.ind_ab_weighted_lebesgue_point`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple (univ : Set (Eucl P)) n M θ ξ → ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
