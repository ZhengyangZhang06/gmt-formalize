# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-localize-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1`
- Child key: `localize`
- Declaration: `Submission.cmc_fc_localize`
- Exact Lean type: `(∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P d : ℕ) (U : Set (Euclid P)) (R : GeometricCurrentOn U (d + 1)), IsOpen U → IsIntegerMultiplicity R → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → R.boundary.massOn W < ∞) → IsIntegerMultiplicity R.boundary) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P m : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)) (W : Set (Euclid P)), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → IsIntegerMultiplicity T → (∀ V : Set (Euclid P), IsOpen V → CompactlyContained V U → ⨆ j, ((Ts j).massOn V + (Ts j).boundary.massOn V) < ∞) → WeaklyConvergesOn Ts T → CompactlyContained W U → ∃ (φ : ℕ → ℕ) (K : Set (Euclid P)) (Λ : NNReal) (Ts' : ℕ → GeometricCurrentOn U (m + 1)) (T' : GeometricCurrentOn U (m + 1)), StrictMono φ ∧ IsCompact K ∧ K ⊆ U ∧ (∀ j, IsIntegerMultiplicity (Ts' j)) ∧ IsIntegerMultiplicity T' ∧ (∀ j, (Ts' j).support ⊆ K) ∧ (∀ j, (Ts' j).mass ≤ Λ ∧ (Ts' j).boundary.mass ≤ Λ) ∧ WeaklyConvergesOn Ts' T' ∧ (∀ (j : ℕ) (ω : TestFormOn U (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ W → Ts' j ω = Ts (φ j) ω) ∧ (∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ W → T' ω = T ω)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
