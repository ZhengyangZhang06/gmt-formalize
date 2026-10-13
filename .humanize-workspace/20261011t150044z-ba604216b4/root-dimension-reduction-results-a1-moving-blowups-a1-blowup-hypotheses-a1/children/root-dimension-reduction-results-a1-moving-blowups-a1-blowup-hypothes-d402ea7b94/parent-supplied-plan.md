# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.moving_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-blowup-hypothes-d402ea7b94/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1`
- Child key: `moving_mass_bound`
- Declaration: `Submission.dimred_mbl_bh_moving_blowUp_mass_bound`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) → ∀ (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (blowUp T (xs j) (lams j) (hlams j).ne').massOn (ball 0 R) ≤ c`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.density_and_tangent_cones-a1.blowup_scaling-a1.mass_scaling-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
