# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1.chart_separation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-c1-submani-ea5ebe33cc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1`
- Child key: `chart_separation`
- Declaration: `Submission.rsod_c1tan_chart_separation`
- Exact Lean type: `∀ (m N : ℕ) (V : Set (Rn m)) (W : Set (EuclideanSpace ℝ (Fin N))) (φ : Rn m → EuclideanSpace ℝ (Fin N)) (v₀ : Rn m), IsOpen W → ContinuousOn φ V → InjOn φ V → v₀ ∈ V → φ v₀ ∈ W → (∀ K : Set (EuclideanSpace ℝ (Fin N)), IsCompact K → K ⊆ W → IsCompact (V ∩ φ ⁻¹' K)) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ V, δ ≤ ‖v - v₀‖ → ε ≤ ‖φ v - φ v₀‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
