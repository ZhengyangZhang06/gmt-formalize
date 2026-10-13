# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-level-slices-rectifiable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1`
- Child key: `c1_level_slices_rectifiable`
- Declaration: `Submission.c1_level_slices_countablyRectifiable`
- Exact Lean type: `∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m), 0 < k → IsOpen D → ContDiffOn ℝ 1 ψ D → ContDiff ℝ 1 G → ∀ᵐ y ∂(volume : Measure (Rn m)), CountablyRectifiable k (ψ '' (D ∩ G ⁻¹' {y}))`

## Sibling prerequisites

- `root.coarea_and_slices-a1.critical_slices-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
