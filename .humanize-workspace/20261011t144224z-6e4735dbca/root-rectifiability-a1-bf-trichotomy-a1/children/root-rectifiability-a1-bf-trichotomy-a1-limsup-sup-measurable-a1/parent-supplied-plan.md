# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.bf_trichotomy-a1.limsup_sup_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-trichotomy-a1-limsup-sup-measurable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.bf_trichotomy-a1`
- Child key: `limsup_sup_measurable`
- Declaration: `Submission.rectifiability_bf_limsup_sup_measurable`
- Exact Lean type: `∀ (Z Y : Type) [MeasurableSpace Z] [MeasurableSpace Y] (k : ℕ) (μ : Measure Y) (δ : ℝ) (G : ℝ → ℝ → Set (Z × Y)), SFinite μ → (∀ r s, MeasurableSet (G r s)) → (∀ r s s', s ≤ s' → G r s ⊆ G r s') → (∀ r s, 0 < r → G r s = ⋃ r' ∈ Ioo (0 : ℝ) r, G r' s) → Measurable (fun z : Z => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {y | (z, y) ∈ G r s} / ENNReal.ofReal ((r * s) ^ k)) (𝓝[>] 0))`

## Sibling prerequisites

- `root.rectifiability-a1.mickle_rado-a1.limsup_eq_iinf-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
