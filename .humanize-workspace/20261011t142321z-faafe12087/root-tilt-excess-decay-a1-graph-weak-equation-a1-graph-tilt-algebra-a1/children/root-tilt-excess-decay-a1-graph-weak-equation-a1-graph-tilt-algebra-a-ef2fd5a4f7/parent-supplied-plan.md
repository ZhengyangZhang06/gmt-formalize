# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1.graph_row_orthogonal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tilt-algebra-a-ef2fd5a4f7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1`
- Child key: `graph_row_orthogonal`
- Declaration: `Submission.gwe_gta_graph_row_orthogonal`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (D : Rn n →L[ℝ] Rn ℓ) (j : Fin ℓ) (r : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ)))) = (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint r 0))`

## Sibling prerequisites

- `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1.graph_coords-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
