# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1.translate_vanish-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-8f4345c036/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1`
- Child key: `translate_vanish`
- Declaration: `Submission.dimred_cs_sos_mt_si_translate_action_eq_zero_of_concentrated`
- Exact Lean type: `∀ (P j : ℕ) (G : Submodule ℝ (Euclid P)) (R : IMRep (univ : Set (Euclid P)) j) (η : DifferentialForm (Euclid P) j), HasCompactSupport η → R.measure (Gᗮ : Set (Euclid P))ᶜ = 0 → ∃ K : Set (Euclid P), IsCompact K ∧ ∀ t ∈ G, t ∉ K → R.action (fun y => η (t + y)) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
