# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1`
- Child key: `slice_family`
- Declaration: `Submission.dor_lmbs_imrep_slice_family`
- Exact Lean type: `(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → ∃ Rs : ℝ → IMRep U n, (∀ t, (Rs t).carrier ⊆ f ⁻¹' {t}) ∧ (∀ W : Set (Euclid P), MeasurableSet W → AEMeasurable (fun t => (Rs t).measure W) ∧ ∫⁻ t, (Rs t).measure W ≤ (L : ℝ≥0∞) * RT.measure W) ∧ (∀ ω : TestFormOn U n, Integrable (fun s => (Rs s).action (ω : DifferentialForm (Euclid P) n))) ∧ ∀ (ω : TestFormOn U n) (a b : ℝ), a < b → ∫ s in a..b, (Rs s).action (ω : DifferentialForm (Euclid P) n) = (b - a) * ((∫ x in RT.carrier, (RT.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier, (RB.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n])`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
