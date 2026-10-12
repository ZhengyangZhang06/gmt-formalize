# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.allard_density_bounds-a1.support_diff_carrier_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-allard-density-bounds-a1-support-diff-carrier-null-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.allard_density_bounds-a1`
- Child key: `support_diff_carrier_null`
- Declaration: `Submission.ted_adb_support_diff_carrier_null`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (W : Set (Amb n ℓ)), IsOpen W → V.weight W < ⊤ → (∀ y ∈ V.support ∩ W, ∃ c : ℝ, 0 < c ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * (unitBallVolume n * s ^ n)) ≤ V.weight (closedBall y s)) → (μHE[n] : Measure (Amb n ℓ)) ((V.support ∩ W) \ V.carrier) = 0`

## Sibling prerequisites

- `root.density_one_regularity-a1.carrier_support_null-a1.upper_density_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
