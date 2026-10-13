# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.hs_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-one-dim-sup-a1-hs-deriv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1`
- Child key: `hs_deriv`
- Declaration: `Submission.tdo_ods_hsNormSq_fderiv_single`
- Exact Lean type: `∀ (ℓ : ℕ) (w : Rn 1 → Rn ℓ) (t : ℝ), hsNormSq (fderiv ℝ w (EuclideanSpace.single (0 : Fin 1) t)) = ‖deriv (fun s : ℝ => w (EuclideanSpace.single (0 : Fin 1) s)) t‖ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
