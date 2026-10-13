# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.bf_trichotomy-a1.cone_ratio_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-trichotomy-a1-cone-ratio-measurable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.bf_trichotomy-a1`
- Child key: `cone_ratio_measurable`
- Declaration: `Submission.rectifiability_bf_cone_ratio_measurable`
- Exact Lean type: `∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ), SFinite μ → Measurable (fun p : Eucl N × (Fin (m + 1) → Eucl N) => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x p.1 < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) (x - p.1)) : Eucl (m + 1))‖ < s * ‖x - p.1‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0))`

## Sibling prerequisites

- `root.rectifiability-a1.bf_trichotomy-a1.limsup_sup_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
