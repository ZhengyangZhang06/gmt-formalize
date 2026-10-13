# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1.set_integral_cauchy_schwarz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-weighted-energy-weak-366e60ba37/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1`
- Child key: `set_integral_cauchy_schwarz`
- Declaration: `Submission.gwe_wewe_setIntegral_le_sqrt_mul_sqrt`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (S : Set X) (g D : X → ℝ), μ S < ⊤ → AEStronglyMeasurable g (μ.restrict S) → IntegrableOn D S μ → (∀ᵐ x ∂(μ.restrict S), 0 ≤ g x ∧ g x ^ 2 ≤ D x) → ∫ x in S, g x ∂μ ≤ Real.sqrt (μ S).toReal * Real.sqrt (∫ x in S, D x ∂μ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
