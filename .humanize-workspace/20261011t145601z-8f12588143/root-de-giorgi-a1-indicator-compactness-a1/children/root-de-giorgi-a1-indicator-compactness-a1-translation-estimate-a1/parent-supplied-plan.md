# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-translation-estimate-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1`
- Child key: `translation_estimate`
- Declaration: `Submission.indCompact_translation_estimate`
- Exact Lean type: `∀ (N : ℕ) (F : Set (Rn N)) (R C : ℝ), NullMeasurableSet F volume → (∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball (0 : Rn N) (R + 1) → (∀ y, ‖g y‖ ≤ 1) → ∫ y in F, Poincare.SimonGMT.Chapter02.euclideanDivergence g y ≤ C) → ∀ h : Rn N, ‖h‖ ≤ 1 → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F) F) ≤ ENNReal.ofReal (C * ‖h‖)`

## Sibling prerequisites

- `root.de_giorgi-a1.indicator_compactness-a1.l1_duality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
