# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1`
- Child key: `ae_blowup`
- Declaration: `Submission.ind_ae_blowup_limit`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple (univ : Set (Eucl P)) n M θ ξ → ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q → ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → HasCompactSupport ω → Tendsto (fun r : ℝ => tauAction n M θ ξ (fun y => (r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))) (𝓝[>] 0) (𝓝 (θ x * ∫ z in (Q : Set (Eucl P)), ξ x (ω z) ∂(μHE[n] : Measure (Eucl P))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
