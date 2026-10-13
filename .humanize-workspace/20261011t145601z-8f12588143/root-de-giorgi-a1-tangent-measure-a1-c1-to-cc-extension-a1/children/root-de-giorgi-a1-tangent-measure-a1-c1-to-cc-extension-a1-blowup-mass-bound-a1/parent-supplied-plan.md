# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1.blowup_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-c1-to-cc-extension-a1-blowup-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1`
- Child key: `blowup_mass_bound`
- Declaration: `Submission.deGiorgiTM_blowUp_integral_bound`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Rn N)) (x : Rn N) (C R r M : ℝ) (h : Rn N → ℝ), 0 < r → 0 < R → μ (Metric.ball x (r * R)) ≤ ENNReal.ofReal (C * (r * R) ^ n) → Continuous h → (∀ z, |h z| ≤ M) → (∀ z, h z ≠ 0 → ‖z‖ < R) → Integrable (fun y ↦ h (blowUpMap x r y)) μ ∧ |(r ^ n)⁻¹ * ∫ y, h (blowUpMap x r y) ∂μ| ≤ M * max C 0 * R ^ n`

## Sibling prerequisites

- `root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1.ball_integral_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
