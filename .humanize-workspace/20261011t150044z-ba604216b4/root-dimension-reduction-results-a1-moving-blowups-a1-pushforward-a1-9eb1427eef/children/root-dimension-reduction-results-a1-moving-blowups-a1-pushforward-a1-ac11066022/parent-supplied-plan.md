# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_current-a1.integrand_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-ac11066022/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_current-a1`
- Child key: `integrand_bound`
- Declaration: `Submission.dimred_mbl_pfc_pullback_integrand_bound`
- Exact Lean type: `∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → ∃ A : ℝ, 0 ≤ A ∧ ∀ (ω : DifferentialForm (Euclid P) n) (B : ℝ), Continuous ω → (∀ z, ‖ω z‖ ≤ B) → Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω (f x)).compContinuousLinearMap (fderiv ℝ f x))) (μHE[n].restrict R.carrier) ∧ |∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]| ≤ A * B`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1.pairing_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
