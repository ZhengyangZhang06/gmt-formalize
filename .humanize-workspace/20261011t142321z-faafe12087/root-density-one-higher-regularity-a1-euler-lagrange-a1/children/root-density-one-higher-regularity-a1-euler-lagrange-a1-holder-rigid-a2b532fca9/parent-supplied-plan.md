# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.euler_lagrange-a1.holder_rigid_transport-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1-holder-rigid-a2b532fca9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.euler_lagrange-a1`
- Child key: `holder_rigid_transport`
- Declaration: `Submission.dohr_vel_holder_rigid_transport`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ) (ξ : Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), IsLocallyHolderCkα q α h U → IsOpen ((fun y => Q (y - ξ)) '' U) ∧ IsLocallyHolderCkα q α (fun z => Q (h (ξ + Q.symm z))) ((fun y => Q (y - ξ)) '' U)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
