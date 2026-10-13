# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1.row_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tilt-algebra-a-b54b49adbc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1`
- Child key: `row_bounds`
- Declaration: `Submission.gwe_gta_row_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), (∀ (j : Fin ℓ) (r : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → ‖r‖ ≤ ‖D‖) ∧ ∃ R : Fin ℓ → Rn n, (∀ (j : Fin ℓ) (v : Rn n), inner ℝ (R j) v = D v j) ∧ ∑ j : Fin ℓ, ‖R j‖ ^ 2 = hsNormSq D`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
