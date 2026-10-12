# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.decay_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-61758856dc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1`
- Child key: `decay_plane`
- Declaration: `Submission.dorag_gc_decay_plane_eq_approxTangent`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t)) → ∀ᵐ x ∂R.measure, x ∈ W → ∀ (S : Submodule ℝ (Euclid P)) (s₀ K : ℝ), 0 < s₀ → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ y in closedBall x s, ENNReal.ofReal (∑ i : Fin P, ‖(approxTangentPlane n R.carrier y).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (K * s ^ (n + 1))) → S = approxTangentPlane n R.carrier x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
