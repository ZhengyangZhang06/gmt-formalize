# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.extension-a1.testform_uniform_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-9f100f3ca4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.extension-a1`
- Child key: `testform_uniform_approx`
- Declaration: `Submission.dimred_mbl_pf_ext_testForm_uniform_approx`
- Exact Lean type: `∀ (P n : ℕ) (h : Euclid P → Covector (Euclid P) n), Continuous h → HasCompactSupport h → ∃ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, TendstoUniformly (fun j x => (ωs j : DifferentialForm (Euclid P) n) x) h atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
