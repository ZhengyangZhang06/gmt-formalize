# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1.tangent_proj_integrands-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tangential-est-a47b8a4457/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1`
- Child key: `tangent_proj_integrands`
- Declaration: `Submission.gte_tangentProj_integrands`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U), (∀ x v : Amb n ℓ, ‖V.tangentProj x v‖ ≤ ‖v‖) ∧ (AEStronglyMeasurable V.tangentProj V.weight → ∀ S : Set (Amb n ℓ), V.weight S < ⊤ → (∀ (e : Amb n ℓ) (g : Amb n ℓ → Amb n ℓ) (C : ℝ), AEStronglyMeasurable g V.weight → (∀ x, ‖g x‖ ≤ C) → IntegrableOn (fun x => inner ℝ (V.tangentProj x e) (V.tangentProj x (g x))) S V.weight) ∧ ∀ T : Submodule ℝ (Amb n ℓ), IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) S V.weight)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
