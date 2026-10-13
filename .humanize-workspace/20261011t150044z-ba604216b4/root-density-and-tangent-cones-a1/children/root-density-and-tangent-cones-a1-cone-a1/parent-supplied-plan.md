# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.cone-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1`
- Child key: `cone`
- Declaration: `Submission.dtc_cone_of_constant_density`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (θ : ℝ), 0 < n → IsIntegerMultiplicity C → BoundaryVanishes C → (∀ R : IMRep (univ : Set (Euclid P)) n, R.Represents C → R.IsStationaryAlong univ) → (∀ ρ : ℝ, 0 < ρ → C.massOn (ball 0 ρ) = unitBallVolume n * ENNReal.ofReal (ρ ^ n) * ENNReal.ofReal θ) → IsConeCurrent C`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
