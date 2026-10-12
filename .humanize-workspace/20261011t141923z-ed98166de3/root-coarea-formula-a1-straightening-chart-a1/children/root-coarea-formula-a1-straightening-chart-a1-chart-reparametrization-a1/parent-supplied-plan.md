# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.straightening_chart-a1.chart_reparametrization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-straightening-chart-a1-chart-reparametrization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.straightening_chart-a1`
- Child key: `chart_reparametrization`
- Declaration: `Submission.coarea_straightening_reparametrize_chart`
- Exact Lean type: `∀ (N m k : ℕ) (M : Set (Rn N)) (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N) (Ω : Set (WithLp 2 (Rn m × Rn k))) (Λ : WithLp 2 (Rn m × Rn k) → Rn (m + k)), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → (∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → IsOpen Ω → ContDiffOn ℝ 1 Λ Ω → InjOn Λ Ω → IsOpen (Λ '' Ω) → Λ '' Ω ⊆ V → (∀ p ∈ Ω, Function.Bijective (fderiv ℝ Λ p)) → ∃ O : Set (Rn N), IsOpen O ∧ (ψ ∘ Λ) '' Ω = O ∩ M ∧ ContDiffOn ℝ 1 (ψ ∘ Λ) Ω ∧ InjOn (ψ ∘ Λ) Ω ∧ (∀ p ∈ Ω, Function.Injective (fderiv ℝ (ψ ∘ Λ) p)) ∧ ∀ p ∈ Ω, tangentSpace M ((ψ ∘ Λ) p) = LinearMap.range (fderiv ℝ (ψ ∘ Λ) p).toLinearMap`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
