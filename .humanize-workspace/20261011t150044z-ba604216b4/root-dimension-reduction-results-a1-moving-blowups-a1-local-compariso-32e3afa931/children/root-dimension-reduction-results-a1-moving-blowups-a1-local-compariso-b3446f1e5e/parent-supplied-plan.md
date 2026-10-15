# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1.region_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-b3446f1e5e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.index_comparison-a1`
- Child key: `region_bound`
- Declaration: `Submission.dimred_mbl_lc_ic_region_bound`
- Exact Lean type: `∀ (P n : ℕ) (U W F B : Set (Euclid P)) (T Z : GeometricCurrentOn U n) (R : IMRep U n) (C S Ŷ Sr Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (e : ℝ≥0∞), IsOpen U → R.Represents T → IsIntegerMultiplicity Z → IsOpen B → B ⊆ U → IsOpen W → IsCompact F → W ⊆ F → F ⊆ B → R.measure (F \ W) = 0 → (S - C).support ⊆ W → IsIntegerMultiplicity Ŷ → Ŷ.support ⊆ F → (∀ R' : IMRep (univ : Set (Euclid P)) n, R'.Represents Ŷ → R'.measure (F \ W) ≤ e) → Sr.mass ≤ e → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → C ω = currentEval T (ω : DifferentialForm (Euclid P) n) + Ŷ ω + Sr ω) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Y ω = (S - C) ω + Ŷ ω) → (∀ ω : TestFormOn U n, Z ω = T ω + Y (testFormOnInclusion (subset_univ U) n ω)) → ∃ b : ℝ≥0∞, T.massOn B = T.massOn W + b ∧ Z.massOn B ≤ S.massOn W + e + e + b`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.compact_outer_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
