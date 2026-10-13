# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tilt_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tilt-algebra-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- Child key: `graph_tilt_algebra`
- Declaration: `Submission.gwe_graph_tilt_algebra`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (D : Rn n →L[ℝ] Rn ℓ), ‖D‖ ≤ 1 → hsNormSq D ≤ ((ℓ : ℝ) + 1 / 2) * hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection - (rotatedPlane q).starProjection) ∧ ∀ (j : Fin ℓ) (r w : Rn n), (∀ v : Rn n, inner ℝ r v = D v j) → |inner ℝ ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint 0 (EuclideanSpace.single j (1 : ℝ))))) ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection (q (graphPoint w 0))) - inner ℝ r w| ≤ hsNormSq ((Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (D v)))).starProjection - (rotatedPlane q).starProjection) * ‖w‖`

## Sibling prerequisites

- `root.tilt_excess_height_estimate-a1.projection_algebra-a1`
- `root.lipschitz_approximation-a1.graph_coordinates-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
