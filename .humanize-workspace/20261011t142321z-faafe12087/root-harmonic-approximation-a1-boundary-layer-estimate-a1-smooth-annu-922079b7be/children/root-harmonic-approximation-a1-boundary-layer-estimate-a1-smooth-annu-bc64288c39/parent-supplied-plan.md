# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1.dilation_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1-smooth-annu-bc64288c39/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.smooth_annulus_estimate-a1`
- Child key: `dilation_formula`
- Declaration: `Submission.ble_sac_lintegral_comp_smul`
- Exact Lean type: `∀ (n : ℕ) (F : Rn n → ℝ≥0∞) (E : Set (Rn n)) (t : ℝ), 0 < t → ∫⁻ x in E, F (t • x) = ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ y in (fun y => t⁻¹ • y) ⁻¹' E, F y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
