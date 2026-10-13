# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.measure_locality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-measure-locality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1`
- Child key: `measure_locality`
- Declaration: `Submission.dtc_bc_measure_restrict_eq_of_eqOn`
- Exact Lean type: `∀ (P n : ℕ) (U₁ U₂ W : Set (Euclid P)) (T₁ : GeometricCurrentOn U₁ n) (T₂ : GeometricCurrentOn U₂ n) (R₁ : IMRep U₁ n) (R₂ : IMRep U₂ n), IsOpen U₁ → IsOpen U₂ → IsOpen W → W ⊆ U₁ → W ⊆ U₂ → R₁.Represents T₁ → R₂.Represents T₂ → (∀ ω : TestFormOn W n, currentEval T₁ (ω : DifferentialForm (Euclid P) n) = currentEval T₂ (ω : DifferentialForm (Euclid P) n)) → R₁.measure.restrict W = R₂.measure.restrict W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
