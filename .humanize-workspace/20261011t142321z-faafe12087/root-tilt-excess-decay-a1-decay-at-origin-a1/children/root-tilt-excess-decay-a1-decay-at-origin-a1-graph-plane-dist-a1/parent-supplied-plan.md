# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1`
- Child key: `graph_plane_dist`
- Declaration: `Submission.tdo_graph_plane_dist`
- Exact Lean type: `∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (A : Rn n →L[ℝ] Rn ℓ), Module.finrank ℝ (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v)))) = n ∧ (∀ x : Amb n ℓ, infDist x (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ≤ infDist x (rotatedPlane q : Set (Amb n ℓ)) + hsNorm A * ‖x‖) ∧ (∀ (x' : Rn n) (y c : Rn ℓ), infDist (q (graphPoint x' y) - q (graphPoint (0 : Rn n) c)) (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ≤ ‖y - (c + A x')‖) ∧ (∀ (x' : Rn n) (y c : Rn ℓ), ‖x'‖ ≤ ‖q (graphPoint x' y) - q (graphPoint (0 : Rn n) c)‖) ∧ ∀ c : Rn ℓ, ‖q (graphPoint (0 : Rn n) c)‖ = ‖c‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
