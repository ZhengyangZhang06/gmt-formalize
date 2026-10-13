# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.graph_height_sup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-height-sup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1`
- Child key: `graph_height_sup`
- Declaration: `Submission.tdo_graph_height_sup`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (c : Rn ℓ) (A : Rn n →L[ℝ] Rn ℓ) (R a r s₀ b β κ : ℝ), 0 ≤ b → 0 < κ → r + s₀ ≤ a → ‖c‖ + r + s₀ ≤ R → (∀ x' ∈ closedBall (0 : Rn n) a, ‖f x' - (c + A x')‖ ≤ b) → V.weight (closedBall 0 R ∩ (V.support \ q '' graphOver f (closedBall 0 R))) ≤ ENNReal.ofReal β → (∀ x ∈ V.support ∩ closedBall (q (graphPoint (0 : Rn n) c)) r, ∀ s : ℝ, 0 < s → s ≤ s₀ → ENNReal.ofReal (κ * s) ≤ V.weight (closedBall x s)) → (∀ x ∈ V.support ∩ closedBall (q (graphPoint (0 : Rn n) c)) r, infDist (x - q (graphPoint (0 : Rn n) c)) (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ≤ 2 * s₀) → ∀ x ∈ V.support ∩ closedBall (q (graphPoint (0 : Rn n) c)) r, infDist (x - q (graphPoint (0 : Rn n) c)) (Submodule.span ℝ (Set.range fun v : Rn n => q (graphPoint v (A v))) : Set (Amb n ℓ)) ≤ max (2 * b) (2 * β / κ)`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_plane_dist-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
