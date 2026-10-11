# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.isoperimetric-a1.lattice_mass_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-lattice-mass-lower-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.isoperimetric-a1`
- Child key: `lattice_mass_lower_bound`
- Declaration: `Submission.isoperimetric_lattice_chain_mass_ge`
- Exact Lean type: `∀ (m N : ℕ) (ρ : ℝ) (β : LatticeFaceIndex (m + 1) N → ℝ) (Pc : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), 0 < ρ → IsLatticeChain ρ β Pc → ∀ F : LatticeFaceIndex (m + 1) N, ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ Pc.mass`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
