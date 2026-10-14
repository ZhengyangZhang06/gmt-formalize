# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_geometry-a1.face_coord-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-90c7d102a6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_geometry-a1`
- Child key: `face_coord`
- Declaration: `Submission.cmcdtfrfg_face_coord`
- Exact Lean type: `∀ (P k : ℕ) (ι : Fin k → Fin P) (b : Fin P → ℤ) (y : Euclid k), Function.Injective ι → (∀ m, (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (ι m) = (b (ι m) : ℝ) + y m) ∧ (∀ l, (∀ m, ι m ≠ l) → (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) l = (b l : ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
