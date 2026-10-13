# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1.localized_first_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-vertical-first-varia-8b0f317ea4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.vertical_first_variation-a1`
- Child key: `localized_first_variation`
- Declaration: `Submission.gwe_vfv_localized_first_variation`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (φ : Amb n ℓ → ℝ) (e : Amb n ℓ) (r s R : ℝ), ContDiff ℝ 1 φ → 0 < r → 2 * r ≤ R → r ≤ s → s ≤ R → closedBall (0 : Amb n ℓ) R ⊆ U → (∀ x ∈ V.support ∩ closedBall 0 R, x ∈ tsupport φ → ‖x‖ < r) → ∫ x in closedBall (0 : Amb n ℓ) s, V.divM (fun y => φ y • e) x ∂V.weight = -∫ x in closedBall (0 : Amb n ℓ) s, φ x * inner ℝ e (H x) ∂V.weight`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_height_excess-a1.ae_mem_support-a1`
- `root.tilt_excess_height_estimate-a1.smooth_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
