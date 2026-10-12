# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.critical_fibers_euclidean-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1`
- Child key: `critical_fibers_euclidean`
- Declaration: `Submission.coarea_critical_fibers_null_euclidean`
- Exact Lean type: `∀ (m k : ℕ) (V : Set (Rn (m + k))) (G : Rn (m + k) → Rn m), IsOpen V → ContDiffOn ℝ 1 G V → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] ({x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ G x)} ∩ G ⁻¹' {y}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
