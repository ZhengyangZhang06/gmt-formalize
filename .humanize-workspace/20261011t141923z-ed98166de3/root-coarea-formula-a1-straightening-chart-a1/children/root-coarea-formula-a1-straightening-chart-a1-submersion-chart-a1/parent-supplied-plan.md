# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.straightening_chart-a1.submersion_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-straightening-chart-a1-submersion-chart-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.straightening_chart-a1`
- Child key: `submersion_chart`
- Declaration: `Submission.coarea_straightening_submersion_chart`
- Exact Lean type: `∀ (m k : ℕ) (V : Set (Rn (m + k))) (G : Rn (m + k) → Rn m) (a : Rn (m + k)), IsOpen V → ContDiffOn ℝ 1 G V → a ∈ V → Function.Surjective (fderiv ℝ G a) → ∃ (Ω : Set (WithLp 2 (Rn m × Rn k))) (Λ : WithLp 2 (Rn m × Rn k) → Rn (m + k)), IsOpen Ω ∧ ContDiffOn ℝ 1 Λ Ω ∧ InjOn Λ Ω ∧ IsOpen (Λ '' Ω) ∧ a ∈ Λ '' Ω ∧ Λ '' Ω ⊆ V ∧ (∀ p ∈ Ω, Function.Bijective (fderiv ℝ Λ p)) ∧ ∀ p ∈ Ω, G (Λ p) = WithLp.fst p`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
