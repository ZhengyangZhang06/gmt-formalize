# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1.lipschitz_fderiv_facts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-weighted-energy-weak-6472e8750e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1`
- Child key: `lipschitz_fderiv_facts`
- Declaration: `Submission.gwe_wewe_lipschitz_fderiv_facts`
- Exact Lean type: `∀ (n ℓ : ℕ) (r : ℝ) (f : Rn n → Rn ℓ), LipschitzOnWith 1 f (closedBall 0 r) → Measurable (fun x => hsNormSq (fderiv ℝ f x)) ∧ (∀ j : Fin ℓ, Measurable (gradient (fun y => f y j))) ∧ (∀ x, 0 ≤ hsNormSq (fderiv ℝ f x)) ∧ (∀ x ∈ ball (0 : Rn n) r, hsNormSq (fderiv ℝ f x) ≤ n ∧ ∀ j : Fin ℓ, ‖gradient (fun y => f y j) x‖ ≤ 1) ∧ ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 r → ∀ j : Fin ℓ, ‖gradient (fun y => f y j) x‖ ^ 2 ≤ hsNormSq (fderiv ℝ f x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
