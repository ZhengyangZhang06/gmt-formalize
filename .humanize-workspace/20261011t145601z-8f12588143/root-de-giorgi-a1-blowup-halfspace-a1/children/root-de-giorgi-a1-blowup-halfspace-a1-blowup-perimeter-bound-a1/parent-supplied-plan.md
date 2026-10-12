# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.blowup_halfspace-a1.blowup_perimeter_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1-blowup-perimeter-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.blowup_halfspace-a1`
- Child key: `blowup_perimeter_bound`
- Declaration: `Submission.deGiorgiHS_blowUp_divergence_bound`
- Exact Lean type: `∀ (N n : ℕ) (E : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N) (x : Rn N) (ρ₁ C : ℝ), (∀ᵐ y ∂μ, ‖ν y‖ = 1) → (∀ ρ ∈ Ioo 0 ρ₁, μ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ r R : ℝ, 0 < r → 0 < R → r * R < ρ₁ → ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball 0 R → ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z = -((r ^ n)⁻¹ * ∫ y, inner ℝ (g (blowUpMap x r y)) (ν y) ∂μ)) → ∀ r R : ℝ, 0 < r → 0 < R → r * R < ρ₁ → ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ Metric.ball 0 R → (∀ y, ‖g y‖ ≤ 1) → ∫ z in blowUpMap x r '' E, Poincare.SimonGMT.Chapter02.euclideanDivergence g z ≤ max C 0 * R ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
