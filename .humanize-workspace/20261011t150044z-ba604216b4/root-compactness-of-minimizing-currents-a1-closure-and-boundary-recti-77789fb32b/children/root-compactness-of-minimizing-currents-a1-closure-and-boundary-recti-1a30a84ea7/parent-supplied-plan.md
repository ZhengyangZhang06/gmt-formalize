# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1.complement_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-1a30a84ea7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1`
- Child key: `complement_bound`
- Declaration: `Submission.cbrldvc_setIntegral_le_sub_of_subset`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (θ : ℝ) (V W : Set (Euclid P)), AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, |g x| ≤ 1) → MeasurableSet V → V ⊆ W → μ W < ∞ → ∫ y in V, g y ∂μ ≤ θ * (μ V).toReal → ∫ y in W, g y ∂μ ≤ (μ W).toReal - (1 - θ) * (μ V).toReal`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
