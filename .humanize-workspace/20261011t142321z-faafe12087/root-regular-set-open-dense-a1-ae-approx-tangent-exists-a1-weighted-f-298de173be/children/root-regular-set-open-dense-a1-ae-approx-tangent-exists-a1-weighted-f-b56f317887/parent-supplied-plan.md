# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.lusin_exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-b56f317887/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1`
- Child key: `lusin_exhaustion`
- Declaration: `Submission.rsod_wfu_lusin_closed_exhaustion`
- Exact Lean type: `∀ (n ℓ : ℕ) (A : Set (Amb n ℓ)) (ϑ : Amb n ℓ → ℝ), MeasurableSet A → (μHE[n] : Measure (Amb n ℓ)) A < ∞ → Measurable ϑ → ∃ C : ℕ → Set (Amb n ℓ), (∀ i, IsClosed (C i) ∧ C i ⊆ A ∧ ContinuousOn ϑ (C i)) ∧ (μHE[n] : Measure (Amb n ℓ)) (A \ ⋃ i, C i) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
