# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.top_dim_lattice_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1`
- Child key: `top_dim_lattice_approx`
- Declaration: `Submission.br_top_dim_lattice_approximation`
- Exact Lean type: `∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsIntegerMultiplicity X → X.mass < ∞ → X.boundary.mass < ∞ → ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) (m + 1) → ℤ) (Pk : ℕ → GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), (∀ k, 0 < ρ k) ∧ (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pk k)) ∧ WeaklyConvergesOn Pk X ∧ (⨆ k, (Pk k).boundary.mass) < ∞`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.lattice_face_stokes-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
