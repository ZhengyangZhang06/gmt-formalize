# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.smul_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-83bdce68be/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1`
- Child key: `smul_continuity`
- Declaration: `Submission.dmcbrcs_testFormOnConverges_smul`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Euclid P)) (ζ : Euclid P → ℝ) (ωs : ℕ → TestFormOn (univ : Set (Euclid P)) k) (ηs : ℕ → TestFormOn U k), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → TestFormOnConverges ωs 0 → (∀ j x, (ηs j : DifferentialForm (Euclid P) k) x = ζ x • (ωs j : DifferentialForm (Euclid P) k) x) → TestFormOnConverges ηs 0`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.smul_leibniz-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
