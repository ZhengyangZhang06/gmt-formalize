# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.box_masses-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-ba02ae4cfd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1`
- Child key: `box_masses`
- Declaration: `Submission.dimred_cs_sos_mt_cm_box_masses`
- Exact Lean type: `∀ (P k m n : ℕ) (g : Fin k → Euclid P) (S A₁ A₂ : GeometricCurrentOn (univ : Set (Euclid P)) n) (R RA₁ RA₂ : IMRep (univ : Set (Euclid P)) n) (R₀ R₀' : IMRep (univ : Set (Euclid P)) m) (r s : ℝ) (B : Set (Euclid P)), Orthonormal ℝ g → 0 < r → r < s → IsOpen B → R.Represents S → RA₁.Represents A₁ → RA₂.Represents A₂ → R₀.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → R₀'.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (Submodule.span ℝ (Set.range g) : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → (∀ A : Set (Euclid P), MeasurableSet A → RA₁.measure A = ∫⁻ t in (Submodule.span ℝ (Set.range g) : Set (Euclid P)) \ {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → (∀ A : Set (Euclid P), MeasurableSet A → RA₂.measure A = ∫⁻ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, R₀'.measure ((fun y => t + y) ⁻¹' A) ∂μHE[k]) → S.massOn ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) = ENNReal.ofReal ((2 * s) ^ k) * R₀.measure B ∧ A₁.massOn ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) = (ENNReal.ofReal ((2 * s) ^ k) - ENNReal.ofReal ((2 * r) ^ k)) * R₀.measure B ∧ A₂.massOn ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' B) = ENNReal.ofReal ((2 * r) ^ k) * R₀'.measure B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
