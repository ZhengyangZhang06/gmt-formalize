# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.key_ineq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-plane-projections-a1-key-ineq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1`
- Child key: `key_ineq`
- Declaration: `Submission.any_radius_gr_pp_key_inequality`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A B : Rn n →L[ℝ] Rn ℓ), 2 * hsNormSq (A - B) ≤ (1 + ‖A‖ ^ 2) * (1 + ‖B‖ ^ 2) * hsNormSq ((Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (A v)))).starProjection - (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v)))).starProjection)`

## Sibling prerequisites

- `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.hs_ideal-a1`
- `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.hs_proj_split-a1`
- `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1.graph_param-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
