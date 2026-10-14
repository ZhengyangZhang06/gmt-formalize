# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.rectifiable_area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-d698709751/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child key: `rectifiable_area_formula`
- Declaration: `Submission.dpf_area_formula_bilipschitz_rectifiable`
- Exact Lean type: `∀ (P n : ℕ) (U M : Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal), IsOpen U → MeasurableSet M → M ⊆ U → CountablyRectifiable n M → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (M ∩ C) ≠ ∞) → ContDiff ℝ 1 φ → LipschitzWith Λ φ → Injective φ → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in φ '' M, g y ∂μHE[n] = ∫⁻ x in M, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (approxTangentPlane n M x)) => inner ℝ (fderiv ℝ φ x (stdOrthonormalBasis ℝ (approxTangentPlane n M x) i)) (fderiv ℝ φ x (stdOrthonormalBasis ℝ (approxTangentPlane n M x) j))))) * g (φ x) ∂μHE[n]`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.bilipschitz_pieces-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
