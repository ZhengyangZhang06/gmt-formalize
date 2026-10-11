# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.classical_tangent-a1.uniform_lower_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-classical-tangent-a1-uniform-lower-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.classical_tangent-a1`
- Child key: `uniform_lower_density`
- Declaration: `Submission.classical_tangent_uniform_lower_density`
- Exact Lean type: `LpMonotonicity → LpDensity → LpSupportRepresentation → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (p : ℝ) (x : Ambient n ℓ), 0 < n → IsOpen U → V.HasMeanCurvatureIn U H → V.MultiplicityGE 1 U → (n : ℝ) < p → V.IsLocallyLp U H p → x ∈ U → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ζ ∈ V.support ∩ closedBall x ρ₀, ∀ s : ℝ, 0 < s → s ≤ ρ₀ → omega n / 2 * s ^ n ≤ V.weight.real (closedBall ζ s)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
