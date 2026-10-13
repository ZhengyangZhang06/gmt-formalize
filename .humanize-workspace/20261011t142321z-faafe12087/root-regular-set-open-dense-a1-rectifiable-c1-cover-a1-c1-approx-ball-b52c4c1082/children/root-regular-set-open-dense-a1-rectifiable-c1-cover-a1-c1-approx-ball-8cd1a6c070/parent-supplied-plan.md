# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1.uniform_taylor_remainder-a1.closed_egoroff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-rectifiable-c1-cover-a1-c1-approx-ball-8cd1a6c070/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1.uniform_taylor_remainder-a1`
- Child key: `closed_egoroff`
- Declaration: `Submission.rsod_c1ab_utr_closed_egoroff`
- Exact Lean type: `∀ (n : ℕ) (g : ℕ → Rn n → ℝ), (∀ k, Measurable (g k)) → ∀ C : Set (Rn n), MeasurableSet C → volume C ≠ ∞ → (∀ x ∈ C, Tendsto (fun k => g k x) atTop (𝓝 0)) → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ A : Set (Rn n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < δ ∧ TendstoUniformlyOn g (fun _ => 0) atTop A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
