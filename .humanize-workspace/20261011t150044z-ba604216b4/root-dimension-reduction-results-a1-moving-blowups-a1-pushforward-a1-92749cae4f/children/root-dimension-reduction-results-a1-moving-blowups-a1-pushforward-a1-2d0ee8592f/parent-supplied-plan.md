# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.extension-a1.action_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-2d0ee8592f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.extension-a1`
- Child key: `action_tendsto`
- Declaration: `Submission.dimred_mbl_pf_ext_action_tendsto`
- Exact Lean type: `∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n) (hs : ℕ → Euclid P → Covector (Euclid P) n) (h : Euclid P → Covector (Euclid P) n), IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → (∀ j, Continuous (hs j)) → Continuous h → TendstoUniformlyOn hs h atTop K → Tendsto (fun j => R.action (hs j)) atTop (𝓝 (R.action h))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
