# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1.blowup_chart_reparam-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-c1-submani-790cdddcc3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1`
- Child key: `blowup_chart_reparam`
- Declaration: `Submission.rsod_c1tan_blowUp_chart_reparam`
- Exact Lean type: `∀ (m N : ℕ) (V : Set (Rn m)) (φ : Rn m → EuclideanSpace ℝ (Fin N)) (v₀ : Rn m) (r : ℝ), IsOpen V → DifferentiableOn ℝ φ V → InjOn φ V → r ≠ 0 → IsOpen {u : Rn m | v₀ + r • u ∈ V} ∧ InjOn (fun u : Rn m => r⁻¹ • (φ (v₀ + r • u) - φ v₀)) {u : Rn m | v₀ + r • u ∈ V} ∧ (fun u : Rn m => r⁻¹ • (φ (v₀ + r • u) - φ v₀)) '' {u : Rn m | v₀ + r • u ∈ V} = Poincare.SimonGMT.Chapter03.blowUpMap (φ v₀) r '' (φ '' V) ∧ ∀ u ∈ {u : Rn m | v₀ + r • u ∈ V}, HasFDerivAt (fun u : Rn m => r⁻¹ • (φ (v₀ + r • u) - φ v₀)) (fderiv ℝ φ (v₀ + r • u)) u`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
