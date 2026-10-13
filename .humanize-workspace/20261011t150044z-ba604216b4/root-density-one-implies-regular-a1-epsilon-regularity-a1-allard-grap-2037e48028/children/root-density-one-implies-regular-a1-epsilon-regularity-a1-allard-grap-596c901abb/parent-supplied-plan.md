# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.vertical_variation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-596c901abb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1`
- Child key: `vertical_variation_bound`
- Declaration: `Submission.dorag_tes_gv_vertical_variation_bound`
- Exact Lean type: `∀ (n m : ℕ), 0 < n → ∀ (U W : Set (Euclid m)) (R : IMRep U n) (H : Euclid m → Euclid m) (κ : ℝ) (ξ : Euclid m) (r : ℝ) (P : Euclid m →L[ℝ] Euclid n) (ζ : Euclid n → ℝ) (G : ℝ) (e : Euclid m), W ⊆ U → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid m → Euclid m, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → 0 < r → closedBall ξ r ⊆ W → (∀ y, ‖P y‖ ≤ ‖y‖) → (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16) → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ‖e‖ ≤ 1 → IntegrableOn (fun x => fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e))) (closedBall ξ r) R.measure ∧ ENNReal.ofReal |∫ x in closedBall ξ r, fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e)) ∂R.measure| ≤ ENNReal.ofReal G * (ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.vertical_field_variation-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.cutoff_extension-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
