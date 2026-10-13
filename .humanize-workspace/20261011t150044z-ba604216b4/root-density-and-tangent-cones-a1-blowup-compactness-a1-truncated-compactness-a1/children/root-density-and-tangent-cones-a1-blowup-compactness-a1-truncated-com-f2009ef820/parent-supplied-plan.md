# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.weak_compactness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-f2009ef820/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1`
- Child key: `weak_compactness`
- Declaration: `Submission.dtc_bc_tc_weak_compactness`
- Exact Lean type: `∀ (P n : ℕ) (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, (Ts j).massOn W < ∞) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), StrictMono φ ∧ WeaklyConvergesOn (fun j => Ts (φ j)) C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
