# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.graph_geometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-d20d6ee052/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child key: `graph_geometry`
- Declaration: `Submission.dorag_lip_graph_cone_hausdorff_bound`
- Exact Lean type: `∀ (n k : ℕ) (T₀ : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (ξ : Euclid (n + k)) (f : Euclid n → Euclid k) (Λ : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, T₀.starProjection (ι v + ι' w) = ι v) → 0 ≤ Λ → Λ ≤ 1 → (∀ v w, ‖f v - f w‖ ≤ Λ * ‖v - w‖) → (∀ x ∈ range (fun v => ξ + ι v + ι' (f v)), ∀ x' ∈ range (fun v => ξ + ι v + ι' (f v)), ‖(x - x') - T₀.starProjection (x - x')‖ ≤ Λ * ‖x - x'‖) ∧ (∀ x ∈ range (fun v => ξ + ι v + ι' (f v)), ∀ r : ℝ, 0 < r → μHE[n] (range (fun v => ξ + ι v + ι' (f v)) ∩ closedBall x r) ≤ ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n * ENNReal.ofReal (r ^ n))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
