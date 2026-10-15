# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.divergence_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-0a0a2c97ba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Child key: `divergence_form`
- Declaration: `Submission.dor_lmb_fcd_fr_divergence_form`
- Exact Lean type: `∀ (P m : ℕ) (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) (g : Euclid (m + 1) → Euclid (m + 1)) (δ : ℝ), StrictMono p.2 → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → 0 < δ → ∃ ω : TestFormOn (univ : Set (Euclid P)) m, (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) m) x) ≤ 1) ∧ (∀ x ∈ tsupport (ω : DifferentialForm (Euclid P) m), ∃ y ∈ tsupport g, dist x (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) ≤ δ) ∧ ∀ y : Euclid (m + 1), exteriorDerivative (ω : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.coordinate_covectors-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
