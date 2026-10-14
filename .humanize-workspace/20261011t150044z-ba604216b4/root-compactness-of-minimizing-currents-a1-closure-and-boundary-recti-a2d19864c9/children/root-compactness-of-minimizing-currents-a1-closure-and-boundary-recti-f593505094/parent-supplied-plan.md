# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1.extderiv_coords-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f593505094/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1`
- Child key: `extderiv_coords`
- Declaration: `Submission.cbr_cipi_plane_extDeriv_coords`
- Exact Lean type: `∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P), Orthonormal ℝ v → ∀ φ : TestFormOn (univ : Set (Euclid P)) d, (∀ i : Fin (d + 1), ContDiff ℝ 1 (fun x : Fin (d + 1) → ℝ => (φ : DifferentialForm (Euclid P) d) (∑ j, x j • v j) (i.removeNth v)) ∧ HasCompactSupport (fun x : Fin (d + 1) → ℝ => (φ : DifferentialForm (Euclid P) d) (∑ j, x j • v j) (i.removeNth v))) ∧ ∀ z : Fin (d + 1) → ℝ, exteriorDerivative (φ : DifferentialForm (Euclid P) d) (∑ j, z j • v j) v = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * fderiv ℝ (fun x : Fin (d + 1) → ℝ => (φ : DifferentialForm (Euclid P) d) (∑ j, x j • v j) (i.removeNth v)) z (Pi.single i 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
