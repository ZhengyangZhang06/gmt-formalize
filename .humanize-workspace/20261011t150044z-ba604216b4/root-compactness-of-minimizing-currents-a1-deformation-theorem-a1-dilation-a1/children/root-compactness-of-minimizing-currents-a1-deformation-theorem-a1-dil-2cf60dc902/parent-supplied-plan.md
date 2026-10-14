# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1.mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-dil-2cf60dc902/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1`
- Child key: `mass`
- Declaration: `Submission.cmcdt_dil_mass_eq`
- Exact Lean type: `∀ (P k : ℕ) (lam : ℝ), 0 < lam → ∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, (∀ ω η : TestFormOn (univ : Set (Euclid P)) k, (η : DifferentialForm (Euclid P) k) = affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) → Y ω = X η) → Y.mass = ENNReal.ofReal (lam ^ k) * X.mass`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1.pullback_testform-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
