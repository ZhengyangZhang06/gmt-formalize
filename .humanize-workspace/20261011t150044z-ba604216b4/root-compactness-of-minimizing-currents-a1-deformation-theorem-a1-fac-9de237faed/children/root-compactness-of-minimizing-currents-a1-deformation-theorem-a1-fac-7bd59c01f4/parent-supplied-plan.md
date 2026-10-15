# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1.face_union_local_plane-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-7bd59c01f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1`
- Child key: `face_union_local_plane`
- Declaration: `Submission.cmcdtfrpi_face_union_local_plane`
- Exact Lean type: `(∀ (P k : ℕ), volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)))) → ∀ (P k : ℕ) (S : Finset ((Fin k → Fin P) × (Fin P → ℤ))), (∀ p ∈ S, StrictMono p.1) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint ((fun y : Euclid k => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}) ((fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1})) ∧ ∀ p ∈ S, ∀ t : Euclid k, (∀ i, 0 < t i ∧ t i < 1) → ∃ δ : ℝ, 0 < δ ∧ ∀ z : Euclid P, dist z (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) < δ → (z ∈ ⋃ q ∈ S, (fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} ↔ z - (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Submodule.span ℝ (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
