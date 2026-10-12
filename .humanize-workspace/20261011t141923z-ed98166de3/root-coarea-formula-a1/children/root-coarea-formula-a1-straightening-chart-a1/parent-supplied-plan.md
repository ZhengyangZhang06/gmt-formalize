# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.straightening_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-straightening-chart-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1`
- Child key: `straightening_chart`
- Declaration: `Submission.coarea_exists_straightening_chart`
- Exact Lean type: `∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m) (x₀ : Rn N), Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → (∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → x₀ ∈ M → coareaJacobian M f x₀ ≠ 0 → ∃ (Ω : Set (WithLp 2 (Rn m × Rn k))) (O : Set (Rn N)) (Ψ : WithLp 2 (Rn m × Rn k) → Rn N), IsOpen Ω ∧ IsOpen O ∧ x₀ ∈ O ∧ ContDiffOn ℝ 1 Ψ Ω ∧ InjOn Ψ Ω ∧ Ψ '' Ω = O ∩ M ∧ (∀ p ∈ Ω, Function.Injective (fderiv ℝ Ψ p)) ∧ (∀ p ∈ Ω, f (Ψ p) = WithLp.fst p) ∧ ∀ p ∈ Ω, tangentSpace M (Ψ p) = LinearMap.range (fderiv ℝ Ψ p).toLinearMap`

## Sibling prerequisites

- `root.coarea_formula-a1.jacobian_linear_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
