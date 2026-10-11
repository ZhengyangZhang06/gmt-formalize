# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_sard-a1.level_set_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-sard-a1-level-set-chart-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_sard-a1`
- Child key: `level_set_chart`
- Declaration: `Submission.c1_sard_submersion_level_set_chart`
- Exact Lean type: `∀ (m k : ℕ) (V : Set (Rn (m + k))) (G : Rn (m + k) → Rn m) (x₀ : Rn (m + k)), IsOpen V → x₀ ∈ V → ContDiffOn ℝ 1 G V → Function.Surjective (fderiv ℝ G x₀) → ∃ (D : Set (Rn k)) (V₁ : Set (Rn (m + k))) (l : Rn k → Rn (m + k)), x₀ ∈ V₁ ∧ V₁ ⊆ V ∧ Chapter02.IsSimonLocalRepresentation 1 (G ⁻¹' {G x₀}) D V₁ l`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
