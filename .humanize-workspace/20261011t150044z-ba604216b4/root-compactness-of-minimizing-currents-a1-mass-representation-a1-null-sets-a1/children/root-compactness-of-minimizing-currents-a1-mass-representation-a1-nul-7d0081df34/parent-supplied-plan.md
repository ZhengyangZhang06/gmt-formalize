# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1.proj_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-nul-7d0081df34/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1`
- Child key: `proj_null`
- Declaration: `Submission.cmr_volume_coordProj_image_null`
- Exact Lean type: `∀ (P n : ℕ) (I : Fin n → Fin P) (C : Set (Euclid P)), Function.Injective I → μHE[n] C = 0 → volume ((fun x : Euclid P => (WithLp.toLp 2 (fun k => x (I k)) : Euclid n)) '' C) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
