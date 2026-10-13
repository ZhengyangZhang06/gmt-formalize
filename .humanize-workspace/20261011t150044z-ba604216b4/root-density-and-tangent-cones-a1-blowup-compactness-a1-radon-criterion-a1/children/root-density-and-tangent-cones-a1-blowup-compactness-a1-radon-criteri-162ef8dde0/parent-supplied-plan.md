# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.radon_criterion-a1.reverse_fatou_upper_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-radon-criteri-162ef8dde0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.radon_criterion-a1`
- Child key: `reverse_fatou_upper_bound`
- Declaration: `Submission.dtc_bc_rc_limsup_lintegral_le`
- Exact Lean type: `∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → limsup (fun j => μs j K) atTop ≤ μ K) → ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → (∀ x, 0 ≤ g x) → limsup (fun j => ∫⁻ x, ENNReal.ofReal (g x) ∂(μs j)) atTop ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
