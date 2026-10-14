# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1`
- Child key: `diffeo_pushforward`
- Declaration: `Submission.imrep_c1_diffeo_pushforward_im`
- Exact Lean type: `∀ (P n : ℕ) (U K : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (φ : Euclid P → Euclid P), IsOpen U → R.Represents T → IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → Bijective φ → (∀ x, Injective (fderiv ℝ φ x)) → (∀ x, x ∉ K → φ x = x) → ∃ S : GeometricCurrentOn U n, IsIntegerMultiplicity S ∧ (BoundaryVanishes T → BoundaryVanishes S) ∧ ∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n]`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.tangent_projection_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
