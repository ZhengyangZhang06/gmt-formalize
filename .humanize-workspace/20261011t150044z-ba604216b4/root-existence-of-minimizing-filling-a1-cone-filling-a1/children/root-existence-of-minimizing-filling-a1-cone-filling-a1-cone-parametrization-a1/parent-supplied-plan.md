# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-parametrization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.existence_of_minimizing_filling-a1.cone_filling-a1`
- Child key: `cone_parametrization`
- Declaration: `Submission.ecf_cone_parametrization`
- Exact Lean type: `∀ (n P : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1)) (R : GeometricCurrentOn (univ : Set (Euclid P)) (n + 2)) (F : ℕ → Euclid (n + 1) → Euclid P) (A : ℕ → Set (Euclid (n + 1))) (g : ℕ → Euclid (n + 1) → ℤ), IsCompact S.support → (∀ j, ∃ K : NNReal, LipschitzWith K (F j)) → (∀ j, MeasurableSet (A j)) → (∀ j, Measurable (g j)) → (∀ j, IntegrableOn (fun u => (g j u : ℝ)) (A j)) → (∀ j, ∀ u ∈ A j, DifferentiableAt ℝ (F j) u) → (∀ j, F j '' A j ⊆ S.support) → ∑' j, ∫⁻ u in A j, ‖(g j u : ℝ)‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (n + 1) => inner ℝ (fderiv ℝ (F j) u (EuclideanSpace.single a 1)) (fderiv ℝ (F j) u (EuclideanSpace.single b 1))))) ≠ ∞ → (∀ ω : TestFormOn (univ : Set (Euclid P)) (n + 1), HasSum (fun j => ∫ u in A j, (g j u : ℝ) * (ω : DifferentialForm (Euclid P) (n + 1)) (F j u) (fun a => fderiv ℝ (F j) u (EuclideanSpace.single a 1))) (S ω)) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (n + 2), ∃ γ : TestFormOn (univ : Set (Euclid P)) (n + 1), R ω = S γ ∧ ∀ x ∈ S.support, ∀ v : Fin (n + 1) → Euclid P, (γ : DifferentialForm (Euclid P) (n + 1)) x v = ∫ t in (0 : ℝ)..1, t ^ (n + 1) * (ω : DifferentialForm (Euclid P) (n + 2)) (t • x) (Fin.cons x v)) → ∃ (G : ℕ → Euclid (n + 2) → Euclid P) (B : ℕ → Set (Euclid (n + 2))) (w : ℕ → Euclid (n + 2) → ℤ), (∀ j, ∃ K : NNReal, LipschitzWith K (G j)) ∧ (∀ j, MeasurableSet (B j)) ∧ (∀ j, Measurable (w j)) ∧ (∀ j, IntegrableOn (fun u => (w j u : ℝ)) (B j)) ∧ ∑' j, ∫⁻ u in B j, ‖(w j u : ℝ)‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (n + 2) => inner ℝ (fderiv ℝ (G j) u (EuclideanSpace.single a 1)) (fderiv ℝ (G j) u (EuclideanSpace.single b 1))))) ≠ ∞ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (n + 2), HasSum (fun j => ∫ u in B j, (w j u : ℝ) * (ω : DifferentialForm (Euclid P) (n + 2)) (G j u) (fun a => fderiv ℝ (G j) u (EuclideanSpace.single a 1))) (R ω)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
