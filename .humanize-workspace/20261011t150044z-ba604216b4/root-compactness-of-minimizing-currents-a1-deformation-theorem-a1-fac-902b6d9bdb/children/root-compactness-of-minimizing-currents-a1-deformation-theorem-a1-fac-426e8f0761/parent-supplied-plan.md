# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_integral_current-a1.coeff_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-426e8f0761/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_integral_current-a1`
- Child key: `coeff_bounds`
- Declaration: `Submission.cmcdtfrfic_coeff_bounds`
- Exact Lean type: `∀ (P k : ℕ) (α : Covector (Euclid P) k), (∀ I : Fin k → Fin P, StrictMono I → |α (fun j => EuclideanSpace.single (I j) (1 : ℝ))| ≤ covectorEuclideanNorm α) ∧ ∀ ι : Fin (k + 1) → Fin P, StrictMono ι → ∑ i : Fin (k + 1), (α (fun j => EuclideanSpace.single (ι (i.succAbove j)) (1 : ℝ))) ^ 2 ≤ covectorEuclideanNorm α ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
