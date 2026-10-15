# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1.pairing_add-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-co-152f19825b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1`
- Child key: `pairing_add`
- Declaration: `Submission.dor_lmb_pc_cm_pairing_add_of_bounded`
- Exact Lean type: `∀ (P n : ℕ) (U K : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (F : Euclid P → Covector (Euclid P) n) (B : ℝ), IsCompact K → K ⊆ U → AEStronglyMeasurable F μHE[n] → (∀ x, x ∉ K → F x = 0) → (∀ x, ‖F x‖ ≤ B) → (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (F x) ∂μHE[n] = ∫ x in R₁.carrier, (R₁.mult x : ℝ) * R₁.orient x (F x) ∂μHE[n] + ∫ x in R₂.carrier, (R₂.mult x : ℝ) * R₂.orient x (F x) ∂μHE[n]`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1.pairing_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
