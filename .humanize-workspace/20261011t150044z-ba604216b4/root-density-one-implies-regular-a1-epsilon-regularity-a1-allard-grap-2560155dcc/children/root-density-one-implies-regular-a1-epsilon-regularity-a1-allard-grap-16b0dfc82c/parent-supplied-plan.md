# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_transfer-a1.exceptional_set-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-16b0dfc82c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_transfer-a1`
- Child key: `exceptional_set`
- Declaration: `Submission.dorag_tes_gt_graph_measure_exceptional_set`
- Exact Lean type: `∀ (n k : ℕ) (U W : Set (Euclid (n + k))) (R : IMRep U n) (ξ : Euclid (n + k)) (r a : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (f : Euclid n → Euclid k), W ⊆ U → 0 < r → closedBall ξ r ⊆ W → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → R.mult x = 1) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ r) ≤ ENNReal.ofReal a → R.measure ((fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2)) ≠ ∞ ∧ ∃ Z : Set (Euclid n), MeasurableSet Z ∧ μHE[n] ((fun v => ξ + ι v + ι' (f v)) '' Z) ≤ ENNReal.ofReal a ∧ ∀ h : Euclid (n + k) → ℝ≥0∞, Measurable h → ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), h x ∂R.measure = ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' (ball (0 : Euclid n) (r / 2) \ Z), h x ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
