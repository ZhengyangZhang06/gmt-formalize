# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.density_gap-a1.cone_ball_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1-cone-ball-mass-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.density_gap-a1`
- Child key: `cone_ball_mass`
- Declaration: `Submission.dimred_cdg_im_cone_ball_mass`
- Exact Lean type: `∀ (P j : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) j), IsConeCurrent C → IsIntegerMultiplicity C → (∀ ρ : ℝ, 0 < ρ → C.massOn (ball 0 ρ) = ENNReal.ofReal (ρ ^ j) * C.massOn (ball 0 1)) ∧ (∀ θ : ℝ, HasMassDensity C 0 θ ↔ 0 ≤ θ ∧ C.massOn (ball 0 1) = unitBallVolume j * ENNReal.ofReal θ) ∧ ∀ θ : ℝ, 0 < θ → HasMassDensity C 0 θ → (0 : Euclid P) ∈ C.support`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
