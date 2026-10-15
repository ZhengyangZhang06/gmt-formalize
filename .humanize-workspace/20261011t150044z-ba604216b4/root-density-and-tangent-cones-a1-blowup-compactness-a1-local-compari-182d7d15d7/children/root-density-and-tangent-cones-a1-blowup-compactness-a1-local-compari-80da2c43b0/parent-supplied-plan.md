# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.change_of_variables-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-80da2c43b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1`
- Child key: `change_of_variables`
- Declaration: `Submission.dtc_bc_lc_pfi_area_change_of_variables`
- Exact Lean type: `∀ (P n : ℕ), (∀ (A : Euclid n →L[ℝ] Euclid P) (L : Euclid P →L[ℝ] Euclid P), Injective (L.comp A) → Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ ((L.comp A) (EuclideanSpace.single k 1)) ((L.comp A) (EuclideanSpace.single l 1)))) ≤ ‖L‖ ^ n * Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1))))) ∧ ∀ (F : Euclid n → Euclid P) (B : Set (Euclid n)), MeasurableSet B → (∀ x ∈ B, DifferentiableAt ℝ F x ∧ Injective (fderiv ℝ F x)) → InjOn F B → MeasurableSet (F '' B) ∧ Measurable (Function.invFunOn F B) ∧ (∀ p : Euclid P → Prop, (∀ᵐ y ∂(μHE[n].restrict (F '' B)), p y) → ∀ᵐ x ∂(volume.restrict B), p (F x)) ∧ ∀ h : Euclid P → ℝ, AEStronglyMeasurable h (μHE[n].restrict (F '' B)) → (IntegrableOn h (F '' B) μHE[n] ↔ IntegrableOn (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ F x (EuclideanSpace.single k 1)) (fderiv ℝ F x (EuclideanSpace.single l 1)))) * h (F x)) B) ∧ ∫ y in F '' B, h y ∂μHE[n] = ∫ x in B, Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ F x (EuclideanSpace.single k 1)) (fderiv ℝ F x (EuclideanSpace.single l 1)))) * h (F x)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_area-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.orient_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
