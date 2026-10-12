# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1.campanato_center_holder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-center-holder-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_campanato-a1`
- Child key: `campanato_center_holder`
- Declaration: `Submission.allard52_campanato_center_holder`
- Exact Lean type: `∀ (n : ℕ), 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ (m k : ℕ) (G c : Rn n → (Rn m →L[ℝ] Rn k)) (A R α : ℝ), 0 ≤ A → 0 < R → 0 < α → α ≤ 1 → Measurable G → (∀ z ∈ closedBall (0 : Rn n) (R / 4), ∀ s : ℝ, 0 < s → s ≤ R / 4 → ∫⁻ x in closedBall z (s / 2), ENNReal.ofReal (hsNormSq (G x - c z)) ≤ ENNReal.ofReal (A * s ^ n * (s / R) ^ (2 * α))) → ∀ x ∈ ball (0 : Rn n) (R / 16), ∀ y ∈ ball (0 : Rn n) (R / 16), hsNorm (c x - c y) ≤ C * Real.sqrt A * (‖x - y‖ / R) ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
