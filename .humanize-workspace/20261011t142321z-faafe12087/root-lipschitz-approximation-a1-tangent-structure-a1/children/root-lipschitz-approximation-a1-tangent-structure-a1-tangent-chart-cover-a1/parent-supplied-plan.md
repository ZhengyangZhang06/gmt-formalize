# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_approximation-a1.tangent_structure-a1.tangent_chart_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-tangent-structure-a1-tangent-chart-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_approximation-a1.tangent_structure-a1`
- Child key: `tangent_chart_cover`
- Declaration: `Submission.lipts_rectifiable_tangent_chart_cover`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (M : Set (Amb n ℓ)), Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ (N : ℕ → Set (Amb n ℓ)) (T : ℕ → Amb n ℓ → Submodule ℝ (Amb n ℓ)), (∀ k, MeasurableSet (N k)) ∧ (∀ k, (μHE[n] : Measure (Amb n ℓ)) (N k) < ⊤) ∧ (∀ k, ContinuousOn (fun x => (T k x).starProjection) (N k)) ∧ (∀ k, ∀ x ∈ N k, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (N k) x (T k x)) ∧ (μHE[n] : Measure (Amb n ℓ)) (M \ ⋃ k, N k) = 0`

## Sibling prerequisites

- `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.projection_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
