# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-2e680a4f9b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child key: `lipschitz_leibniz`
- Declaration: `Submission.dor_lmbsf_lipschitz_cutoff_leibniz`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal) (g : Euclid P → Euclid P), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → Measurable g → (∀ x, ‖g x‖ ≤ L) → (∀ (a b : ℝ), a < b → ∀ (hs : ℕ → Euclid P → ℝ) (c : ℝ), (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) → TendstoUniformly hs (fun x => min 1 (max 0 ((b - f x) / (b - a)))) atTop → ∀ (W : Euclid P → Euclid P) (K : Set (Euclid P)) (c' : ℝ), Measurable W → IsCompact K → K ⊆ U → (∀ x, x ∉ K → W x = 0) → (∀ x, ‖W x‖ ≤ c') → (∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier), W x ∈ approxTangentPlane (n + 1) RT.carrier x) → Tendsto (fun k => ∫ x in RT.carrier, (RT.mult x : ℝ) * fderiv ℝ (hs k) x (W x) ∂μHE[n + 1]) atTop (𝓝 (∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b}, (RT.mult x : ℝ) * (-(b - a)⁻¹ * inner ℝ (g x) (W x)) ∂μHE[n + 1]))) → ∀ (ω : TestFormOn U n) (a b : ℝ), a < b → ∫ x in RB.carrier, (RB.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] = (∫ x in RT.carrier, (RT.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - (b - a)⁻¹ * ∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b}, (RT.mult x : ℝ) * RT.orient x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight ((ω : DifferentialForm (Euclid P) n) x))) ∂μHE[n + 1]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
