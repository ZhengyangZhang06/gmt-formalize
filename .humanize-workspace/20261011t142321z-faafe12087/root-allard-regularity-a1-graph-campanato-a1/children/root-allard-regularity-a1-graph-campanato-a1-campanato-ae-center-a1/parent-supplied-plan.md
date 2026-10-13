# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.campanato_ae_center-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-ae-center-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1`
- Child key: `campanato_ae_center`
- Declaration: `Submission.allard52_campanato_ae_center`
- Exact Lean type: `∀ (n m k : ℕ) (G c : Rn n → (Rn m →L[ℝ] Rn k)) (A R α B : ℝ), 1 ≤ n → 0 < R → 0 < α → Measurable G → (∀ x, ‖G x‖ ≤ B) → (∀ z ∈ closedBall (0 : Rn n) (R / 4), ∀ s : ℝ, 0 < s → s ≤ R / 4 → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - c z)) ≤ ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α))) → ∀ᵐ z ∂(volume : Measure (Rn n)), z ∈ ball (0 : Rn n) (R / 4) → G z = c z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
