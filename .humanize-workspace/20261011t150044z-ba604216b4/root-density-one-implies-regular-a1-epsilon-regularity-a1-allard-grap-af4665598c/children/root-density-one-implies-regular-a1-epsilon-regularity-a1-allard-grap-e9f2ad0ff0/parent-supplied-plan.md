# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.plane_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-e9f2ad0ff0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child key: `plane_reduction`
- Declaration: `Submission.dorag_tes_plane_reduction`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclid N)) (Q : Euclid N → Submodule ℝ (Euclid N)) (ξ : Euclid N) (σ a M h₁ : ℝ) (T T₁ : Submodule ℝ (Euclid N)), 0 < σ → 0 ≤ a → 0 < M → AEStronglyMeasurable (fun x => (Q x).starProjection) μ → ENNReal.ofReal M ≤ μ (closedBall ξ σ) → ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₁.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal a → (∀ x ∈ μ.support ∩ closedBall ξ σ, ‖(x - ξ) - T₁.starProjection (x - ξ)‖ ≤ h₁) → ∃ S : Submodule ℝ (Euclid N), (S = T ∨ S = T₁) ∧ ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal a ∧ ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ∧ ∀ x ∈ μ.support ∩ closedBall ξ σ, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ h₁ + Real.sqrt (4 * a / M) * σ`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.proj_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
