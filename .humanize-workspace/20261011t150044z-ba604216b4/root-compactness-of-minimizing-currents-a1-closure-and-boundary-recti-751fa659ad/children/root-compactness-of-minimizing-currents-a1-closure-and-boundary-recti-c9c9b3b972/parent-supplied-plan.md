# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.atoms-a1.density_atom-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c9c9b3b972/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.atoms-a1`
- Child key: `density_atom`
- Declaration: `Submission.cbr_ci_cp_atm_liminf_density_le_atom`
- Exact Lean type: `∀ (P n : ℕ) (σ : Measure (Euclid P)) (z : Euclid P) (f : ℝ → ℝ≥0∞), (∀ K : Set (Euclid P), IsCompact K → σ K < ∞) → (∀ r : ℝ, 0 < r → f r ≤ unitBallVolume n * ENNReal.ofReal (r ^ n) * σ (ball z r)) → liminf (fun r : ℝ => f r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) ≤ σ {z}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
