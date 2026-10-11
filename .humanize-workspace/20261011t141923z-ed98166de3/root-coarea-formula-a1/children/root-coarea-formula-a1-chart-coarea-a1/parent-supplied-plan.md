# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.chart_coarea-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-chart-coarea-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1`
- Child key: `chart_coarea`
- Declaration: `Submission.coarea_formula_on_straightening_chart`
- Exact Lean type: `∀ (N m k : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (Ω : Set (WithLp 2 (Rn m × Rn k))) (Ψ : WithLp 2 (Rn m × Rn k) → Rn N) (S : Set (Rn N)) (g : Rn N → ℝ≥0∞), IsOpen Ω → ContDiffOn ℝ 1 Ψ Ω → InjOn Ψ Ω → (∀ p ∈ Ω, Function.Injective (fderiv ℝ Ψ p)) → (∀ p ∈ Ω, DifferentiableAt ℝ f (Ψ p)) → (∀ p ∈ Ω, f (Ψ p) = WithLp.fst p) → (∀ p ∈ Ω, tangentSpace M (Ψ p) = LinearMap.range (fderiv ℝ Ψ p).toLinearMap) → MeasurableSet S → S ⊆ Ψ '' Ω → Measurable g → Measurable (fun y ↦ ∫⁻ x in S ∩ f ⁻¹' {y}, g x ∂μHE[k]) ∧ ∫⁻ x in S, g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] = ∫⁻ y, ∫⁻ x in S ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂volume`

## Sibling prerequisites

- `root.coarea_formula-a1.jacobian_linear_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
