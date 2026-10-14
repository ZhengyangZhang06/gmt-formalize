# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.closure_compact-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-f30aba5c31/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1`
- Child key: `closure_compact`
- Declaration: `Submission.dtc_bc_tc_cl_closure_compact_support`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 1 ≤ c ∧ ∀ Z : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Z → IsCompact Z.support → Z.boundary = 0 → Z.mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity Y ∧ Y.boundary = Z ∧ Y.mass ≤ ENNReal.ofReal (c * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1)) * Z.mass.toReal) ∧ Y.support ⊆ thickening (3 * Real.sqrt P * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1))) Z.support) → ∀ (P d : ℕ), d + 1 < P → (∀ (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U d) (T : GeometricCurrentOn U d), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T) → (∀ (U : Set (Euclid P)) (R : GeometricCurrentOn U (d + 1)), IsOpen U → IsIntegerMultiplicity R → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → R.boundary.massOn W < ∞) → IsIntegerMultiplicity R.boundary) → (∀ (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (T : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (K : Set (Euclid P)), IsCompact K → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ j, IsIntegerMultiplicity (Ts j).boundary) → (∀ j, (Ts j).support ⊆ K) → ⨆ j, ((Ts j).mass + (Ts j).boundary.mass) < ∞ → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.slicing-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.restrict_unique-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.foundations-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.lower_density-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
