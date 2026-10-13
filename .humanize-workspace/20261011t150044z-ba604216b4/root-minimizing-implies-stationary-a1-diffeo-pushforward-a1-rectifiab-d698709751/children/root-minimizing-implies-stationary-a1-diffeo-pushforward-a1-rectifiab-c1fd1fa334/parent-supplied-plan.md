# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.rectifiable_area_formula-a1.piece_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-c1fd1fa334/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.rectifiable_area_formula-a1`
- Child key: `piece_area`
- Declaration: `Submission.dpf_raf_piece_area_formula_gram`
- Exact Lean type: `∀ (P n : ℕ) (Q : Euclid P → Submodule ℝ (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal) (F : Euclid n → Euclid P) (L : NNReal) (B : Set (Euclid n)), Differentiable ℝ φ → LipschitzWith Λ φ → LipschitzWith L F → MeasurableSet B → InjOn F B → InjOn φ (F '' B) → (∀ᵐ b ∂(volume.restrict B), Q (F b) = LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in φ '' (F '' B), g y ∂μHE[n] = ∫⁻ x in F '' B, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (fderiv ℝ φ x (stdOrthonormalBasis ℝ (Q x) i)) (fderiv ℝ φ x (stdOrthonormalBasis ℝ (Q x) j))))) * g (φ x) ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
