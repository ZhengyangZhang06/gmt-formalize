# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_plane_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1`
- Child key: `graph_plane_algebra`
- Declaration: `Submission.allard52_graph_plane_algebra`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∃ L₀ : ℝ, 0 < L₀ ∧ L₀ ≤ 1 / 4 ∧ (∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A B : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ L₀ → hsNorm B ≤ L₀ → hsNormSq (A - B) ≤ hsNormSq (((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection - ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).map q.toLinearEquiv.toLinearMap).starProjection) ∧ hsNormSq (((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection - ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).map q.toLinearEquiv.toLinearMap).starProjection) ≤ 3 * hsNormSq (A - B)) ∧ (∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ L₀ → hsNormSq A ≤ hsNormSq (((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection - (rotatedPlane q).starProjection)) ∧ (∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ) (x : Rn n) (y : Rn ℓ), ‖A‖ ≤ 1 → ‖y - A x‖ ≤ 2 * ‖q (graphPoint x y) - ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection (q (graphPoint x y))‖) ∧ (∀ A : Rn n →L[ℝ] Rn ℓ, ‖A‖ ≤ hsNorm A ∧ hsNorm A ≤ Real.sqrt n * ‖A‖) ∧ (∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → ∃ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, rotatedPlane q = T) ∧ (∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, Continuous fun A : Rn n →L[ℝ] Rn ℓ => ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v))).map q.toLinearEquiv.toLinearMap).starProjection)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
