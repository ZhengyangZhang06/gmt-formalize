# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2560155dcc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child key: `graph_transfer`
- Declaration: `Submission.dorag_tes_graph_parameter_transfer`
- Exact Lean type: `∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (ξ : Euclid (n + k)) (r a : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (f : Euclid n → Euclid k), IsOpen W → W ⊆ U → 0 < r → closedBall ξ r ⊆ W → 0 ≤ a → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → R.mult x = 1) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ r) ≤ ENNReal.ofReal a → (∀ (g : Euclid n → ℝ) (G : ℝ), Measurable g → (∀ v, 0 ≤ g v) → (∀ v, g v ≤ G) → (∫⁻ v in ball (0 : Euclid n) (r / 2), ENNReal.ofReal (g v)) ≤ (∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ENNReal.ofReal (g (P (x - ξ))) ∂R.measure) + ENNReal.ofReal (G * a)) ∧ ∀ (g : Euclid n → ℝ) (G : ℝ), Measurable g → (∀ v, |g v| ≤ G) → |(∫ v in ball (0 : Euclid n) (r / 2), g v) - (∫ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), g (P (x - ξ)) ∂R.measure)| ≤ G * (a + 2 ^ n * (∫ v in ball (0 : Euclid n) (r / 2), ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_area-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
