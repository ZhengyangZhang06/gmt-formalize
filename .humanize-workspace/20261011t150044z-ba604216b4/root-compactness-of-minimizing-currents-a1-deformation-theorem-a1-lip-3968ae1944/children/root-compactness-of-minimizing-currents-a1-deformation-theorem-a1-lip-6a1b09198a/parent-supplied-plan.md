# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-6a1b09198a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Child key: `cutoff`
- Declaration: `Submission.cmcdt_lpo_cutoff_pullback`
- Exact Lean type: `∀ (N N' k : ℕ) (F : Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k) (K : Set (Euclid N)), ContDiff ℝ (⊤ : ℕ∞) F → IsCompact K → ∃ (η : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) ∧ ∀ x ∈ W, exteriorDerivative (η : DifferentialForm (Euclid N) k) x = (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
