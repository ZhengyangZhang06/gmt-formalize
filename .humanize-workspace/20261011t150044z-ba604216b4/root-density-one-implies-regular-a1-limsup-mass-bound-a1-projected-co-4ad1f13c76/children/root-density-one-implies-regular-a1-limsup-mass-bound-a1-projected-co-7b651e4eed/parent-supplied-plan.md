# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1.integral_le_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-co-7b651e4eed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1`
- Child key: `integral_le_measure`
- Declaration: `Submission.dor_lmb_pc_cm_ofReal_integral_le_measure`
- Exact Lean type: `∀ (P n : ℕ) (U G : Set (Euclid P)) (R : IMRep U n) (g : Euclid P → ℝ) (c : ℝ), MeasurableSet G → (∀ᵐ x ∂(μHE[n].restrict R.carrier), |g x| ≤ G.indicator (fun _ => c) x) → ENNReal.ofReal (∫ x in R.carrier, (R.mult x : ℝ) * g x ∂μHE[n]) ≤ ENNReal.ofReal c * R.measure G`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
