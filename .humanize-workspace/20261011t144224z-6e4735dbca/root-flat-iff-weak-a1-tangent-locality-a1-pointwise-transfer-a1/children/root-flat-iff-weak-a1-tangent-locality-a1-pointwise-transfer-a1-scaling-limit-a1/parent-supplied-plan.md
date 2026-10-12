# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1.scaling_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1-scaling-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1`
- Child key: `scaling_limit`
- Declaration: `Submission.fiw_tl_tr_scaling_limit`
- Exact Lean type: `∀ (n : ℕ) (D : ℝ → ℝ) (E G : ℝ → ℝ≥0∞) (R K C : ℝ), 0 < R → (∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝[>] (0 : ℝ), E s ≤ ENNReal.ofReal ε * G s) → (∀ᶠ s in 𝓝[>] (0 : ℝ), G s ≤ ENNReal.ofReal (C * s ^ n)) → (∀ᶠ r in 𝓝[>] (0 : ℝ), ‖D r‖ₑ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal K * E (R * r)) → Tendsto D (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
