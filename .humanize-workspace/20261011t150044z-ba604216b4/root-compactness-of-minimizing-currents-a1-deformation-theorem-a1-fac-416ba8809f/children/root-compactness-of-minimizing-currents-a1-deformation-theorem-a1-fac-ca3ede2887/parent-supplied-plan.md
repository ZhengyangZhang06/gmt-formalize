# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.pullback_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-ca3ede2887/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1`
- Child key: `pullback_divergence`
- Declaration: `Submission.cmcdtfrcb_pullback_divergence`
- Exact Lean type: `∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (a : Euclid P) (γ : DifferentialForm (Euclid P) m), ContDiff ℝ 1 γ → (∀ i : Fin (m + 1), ContDiff ℝ 1 (fun y : Euclid (m + 1) => (-1 : ℝ) ^ (i : ℕ) * γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)))) ∧ ∀ y : Euclid (m + 1), exteriorDerivative γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = ∑ i : Fin (m + 1), fderiv ℝ (fun z : Euclid (m + 1) => (-1 : ℝ) ^ (i : ℕ) * γ (a + ∑ j, z j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) y (EuclideanSpace.single i (1 : ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
