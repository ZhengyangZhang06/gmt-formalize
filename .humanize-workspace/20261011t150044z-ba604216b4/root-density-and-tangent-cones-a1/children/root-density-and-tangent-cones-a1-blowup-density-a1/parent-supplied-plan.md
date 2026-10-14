# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1`
- Child key: `blowup_density`
- Declaration: `Submission.dtc_blowUp_density`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (x : Euclid P) (θ : ℝ) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), IsOpen U → 0 < n → x ∈ U → IsIntegerMultiplicity T → IsIntegerMultiplicity C → Tendsto lams atTop (𝓝 0) → HasMassDensity T x θ → MassMeasuresConverge (fun j => blowUp T x (lams j) (hlams j).ne') C → (∀ ρ : ℝ, 0 < ρ → C.massOn (ball 0 ρ) = unitBallVolume n * ENNReal.ofReal (ρ ^ n) * ENNReal.ofReal θ) ∧ HasMassDensity C 0 θ`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`
- `root.density_and_tangent_cones-a1.blowup_scaling-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
