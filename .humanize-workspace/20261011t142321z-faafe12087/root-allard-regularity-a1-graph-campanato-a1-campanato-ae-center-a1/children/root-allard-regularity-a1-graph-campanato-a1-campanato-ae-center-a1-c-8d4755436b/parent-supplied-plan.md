# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.campanato_ae_center-a1.center_eq_at_lebesgue_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-ae-center-a1-c-8d4755436b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1.campanato_ae_center-a1`
- Child key: `center_eq_at_lebesgue_point`
- Declaration: `Submission.allard52_cae_center_eq_at_lebesgue_point`
- Exact Lean type: `∀ (n m k : ℕ) (G : Rn n → (Rn m →L[ℝ] Rn k)) (z : Rn n) (T : Rn m →L[ℝ] Rn k) (A R α s₀ : ℝ), 0 < R → 0 < α → 0 < s₀ → Measurable G → Tendsto (fun t : ℝ => (volume (closedBall z t))⁻¹ * ∫⁻ x in closedBall z t, ENNReal.ofReal (hsNormSq (G x - G z))) (𝓝[>] 0) (𝓝 0) → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - T)) ≤ ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α))) → G z = T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
