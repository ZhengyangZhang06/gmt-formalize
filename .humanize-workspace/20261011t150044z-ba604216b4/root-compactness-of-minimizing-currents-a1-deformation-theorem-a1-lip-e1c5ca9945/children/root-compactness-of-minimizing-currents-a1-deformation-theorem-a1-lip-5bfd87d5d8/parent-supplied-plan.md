# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1.pullback_le-a1.hs_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-5bfd87d5d8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1.pullback_le-a1`
- Child key: `hs_sum`
- Declaration: `Submission.cmcdt_lp_pullback_basis_sq_sum_le`
- Exact Lean type: `∀ (N N' m : ℕ) (A : Euclid N →L[ℝ] Euclid N') (γ : Covector (Euclid N') m), ∑ j : Fin m → Fin N, ((γ.compContinuousLinearMap A) (fun i => EuclideanSpace.basisFun (Fin N) ℝ (j i))) ^ 2 ≤ (‖A‖ ^ 2) ^ m * ∑ j : Fin m → Fin N', (γ (fun i => EuclideanSpace.basisFun (Fin N') ℝ (j i))) ^ 2`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.grad_norm_sq-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
