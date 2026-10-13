# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1.gram_basis_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-3f0e6c2b24/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1`
- Child key: `gram_basis_invariance`
- Declaration: `Submission.dpf_det_gram_stdOrthonormalBasis_eq`
- Exact Lean type: `∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P) (τ : Fin n → Euclid P), Orthonormal ℝ τ → Submodule.span ℝ (Set.range τ) = Q → Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ Q) => inner ℝ (L (stdOrthonormalBasis ℝ Q i)) (L (stdOrthonormalBasis ℝ Q j))) = Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (L (τ i)) (L (τ j)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
