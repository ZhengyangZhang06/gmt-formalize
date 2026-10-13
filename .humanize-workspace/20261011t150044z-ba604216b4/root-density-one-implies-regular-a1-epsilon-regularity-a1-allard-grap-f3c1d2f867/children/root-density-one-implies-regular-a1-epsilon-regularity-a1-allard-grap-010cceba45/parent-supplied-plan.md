# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.smoothed_bounds-a1.annulus_sandwich-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-010cceba45/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.smoothed_bounds-a1`
- Child key: `annulus_sandwich`
- Declaration: `Submission.doragm_sab_annulus_increment_sandwich`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (q F : Euclid P → ℝ) (A s t : ℝ), 1 < A → 0 < s → s ≤ t → Antitone φ → (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → (∀ x, 0 ≤ q x) → (∀ x, s < ‖x - y‖ → F x = q x) → Integrable (fun x => φ (‖x - y‖ / s) * q x) μ → Integrable (fun x => φ (‖x - y‖ / t) * q x) μ → 0 ≤ (∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ ∧ (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ) ∧ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ) ≤ ∫⁻ x in closedBall y (A * t) \ closedBall y s, ENNReal.ofReal (F x) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
