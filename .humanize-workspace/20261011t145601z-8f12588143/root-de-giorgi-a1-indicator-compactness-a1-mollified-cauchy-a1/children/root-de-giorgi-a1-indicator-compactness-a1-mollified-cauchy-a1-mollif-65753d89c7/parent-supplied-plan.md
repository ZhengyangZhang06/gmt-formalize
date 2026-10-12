# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1.mollifier_l1_error-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-mollified-cauchy-a1-mollif-65753d89c7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1`
- Child key: `mollifier_l1_error`
- Declaration: `Submission.indCompact_mollCauchy_l1_error`
- Exact Lean type: `∀ (N : ℕ) (F : Set (Rn N)) (ρ : Rn N → ℝ) (σ R C : ℝ), NullMeasurableSet F volume → Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 → Function.support ρ ⊆ Metric.closedBall (0 : Rn N) σ → 0 ≤ C → (∀ h : Rn N, ‖h‖ ≤ σ → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F) F) ≤ ENNReal.ofReal (C * ‖h‖)) → ∫⁻ y in Metric.ball (0 : Rn N) R, ENNReal.ofReal |(∫ z in F, ρ (y - z)) - F.indicator (fun _ ↦ (1 : ℝ)) y| ≤ ENNReal.ofReal (σ * C)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
