# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.regraph-a1.inverse_c1-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-regraph-a1-inverse-c1-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1.regraph-a1`
- Child key: `inverse_c1`
- Declaration: `Submission.arp_rgr_right_inverse_contDiffOn`
- Exact Lean type: `∀ {n : ℕ} (Φ X : Rn n → Rn n) (U W : Set (Rn n)) (κ : ℝ), IsOpen U → IsOpen W → 0 < κ → ContDiffOn ℝ 1 Φ U → (∀ x ∈ U, ∀ h : Rn n, κ * ‖h‖ ≤ ‖fderiv ℝ Φ x h‖) → ContinuousOn X W → (∀ w ∈ W, X w ∈ U ∧ Φ (X w) = w) → ContDiffOn ℝ 1 X W ∧ ∀ w ∈ W, ‖fderiv ℝ X w‖ ≤ κ⁻¹`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
