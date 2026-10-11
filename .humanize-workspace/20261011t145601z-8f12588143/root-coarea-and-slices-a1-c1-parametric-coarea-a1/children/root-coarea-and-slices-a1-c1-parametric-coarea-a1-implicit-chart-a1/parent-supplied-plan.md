# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_parametric_coarea-a1.implicit_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-implicit-chart-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1`
- Child key: `implicit_chart`
- Declaration: `Submission.pcoarea_implicit_chart`
- Exact Lean type: `∀ (m k : ℕ) (G : Rn (m + k) → Rn m) (D : Set (Rn (m + k))) (u₀ : Rn (m + k)), IsOpen D → u₀ ∈ D → ContDiff ℝ 1 G → Function.Surjective (fderiv ℝ G u₀) → ∃ Φ : OpenPartialHomeomorph (Rn (m + k)) (WithLp 2 (Rn m × Rn k)), u₀ ∈ Φ.source ∧ Φ.source ⊆ D ∧ ContDiffOn ℝ 1 Φ Φ.source ∧ ContDiffOn ℝ 1 Φ.symm Φ.target ∧ ∀ u ∈ Φ.source, (Φ u).fst = G u`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
