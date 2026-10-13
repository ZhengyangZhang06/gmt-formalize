# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.slice_tonelli-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-3fc66b1738/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child key: `slice_tonelli`
- Declaration: `Submission.dor_lmbsf_pc_slice_area_tonelli`
- Exact Lean type: `∀ (P n : ℕ) (Φ : Euclid (n + 1) → Euclid P) (S : Set (Euclid (n + 1))), MeasurableSet S → (∀ w ∈ S, DifferentiableAt ℝ Φ w) → (∀ w ∈ S, Injective (fderiv ℝ Φ w)) → InjOn Φ S → ∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t : ℝ => ∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n]) = ∫⁻ w in S, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i.succ 1)) (fderiv ℝ Φ w (EuclideanSpace.single j.succ 1))))) * φ (Φ w) ∂volume`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_area-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
