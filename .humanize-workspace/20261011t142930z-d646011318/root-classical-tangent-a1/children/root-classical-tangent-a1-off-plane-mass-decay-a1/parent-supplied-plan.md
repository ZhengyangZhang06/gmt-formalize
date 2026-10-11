# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.classical_tangent-a1.off_plane_mass_decay-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-classical-tangent-a1-off-plane-mass-decay-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.classical_tangent-a1`
- Child key: `off_plane_mass_decay`
- Declaration: `Submission.classical_tangent_off_plane_mass_decay`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (x : Ambient n ℓ) (P : Submodule ℝ (Ambient n ℓ)) (ε : ℝ), IsFiniteMeasureOnCompacts V.weight → V.IsApproxTangentAt x P → 0 < ε → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * V.weight.real (closedBall x ρ \ {y | infDist (y - x) (P : Set (Ambient n ℓ)) < ε * ρ})) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
