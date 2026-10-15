# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1.cutoff_multiplier-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6cedfe64f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1`
- Child key: `cutoff_multiplier`
- Declaration: `Submission.cbrcs_ce_cutoff_multiplier`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Euclid P)) (ζ : Euclid P → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∃ M : TestFormOn (univ : Set (Euclid P)) k →ₗ[ℝ] TestFormOn U k, (∀ (ω : TestFormOn (univ : Set (Euclid P)) k) (x : Euclid P), (M ω : DifferentialForm (Euclid P) k) x = ζ x • (ω : DifferentialForm (Euclid P) k) x) ∧ ∀ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) k, TestFormOnConverges ωs 0 → TestFormOnConverges (fun j => M (ωs j)) 0`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1.leibniz_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
