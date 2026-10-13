# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.hs_integral_compare-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2fff1c16a4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1`
- Child key: `hs_integral_compare`
- Declaration: `Submission.dorag_ted_hs_integral_compare`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (τ : Euclid P → (Euclid P →L[ℝ] Euclid P)) (A₁ A₂ : Euclid P →L[ℝ] Euclid P) (s : Set (Euclid P)), AEStronglyMeasurable τ μ → ENNReal.ofReal (∑ i : Fin P, ‖A₁ (EuclideanSpace.single i (1 : ℝ)) - A₂ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * μ s ≤ 2 * (∫⁻ x in s, ENNReal.ofReal (∑ i : Fin P, ‖τ x (EuclideanSpace.single i (1 : ℝ)) - A₁ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ) + 2 * (∫⁻ x in s, ENNReal.ofReal (∑ i : Fin P, ‖τ x (EuclideanSpace.single i (1 : ℝ)) - A₂ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ) ∧ (∫⁻ x in s, ENNReal.ofReal (∑ i : Fin P, ‖τ x (EuclideanSpace.single i (1 : ℝ)) - A₁ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ) ≤ 2 * (∫⁻ x in s, ENNReal.ofReal (∑ i : Fin P, ‖τ x (EuclideanSpace.single i (1 : ℝ)) - A₂ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ) + 2 * ENNReal.ofReal (∑ i : Fin P, ‖A₁ (EuclideanSpace.single i (1 : ℝ)) - A₂ (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * μ s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
