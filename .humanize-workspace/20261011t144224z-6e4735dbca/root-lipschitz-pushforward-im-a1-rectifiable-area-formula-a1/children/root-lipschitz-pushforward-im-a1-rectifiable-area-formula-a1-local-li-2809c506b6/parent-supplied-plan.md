# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-local-li-2809c506b6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
- Child key: `local_lipschitz_area`
- Declaration: `Submission.lpf_raf_local_lipschitz_area`
- Exact Lean type: `∀ (n Q : ℕ) (Ω D : Set (Eucl n)) (u : Eucl n → Eucl Q) (w : Eucl n → ℝ≥0∞), IsOpen Ω → LocallyLipschitzOn Ω u → D ⊆ Ω → NullMeasurableSet D (volume : Measure (Eucl n)) → AEMeasurable w ((volume : Measure (Eucl n)).restrict D) → AEMeasurable (fun y => ∑' x : {x : Eucl n // x ∈ D ∧ u x = y}, w x) (μHE[n] : Measure (Eucl Q)) ∧ ∫⁻ x in D, w x * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ u x (EuclideanSpace.single i 1)) (fderiv ℝ u x (EuclideanSpace.single j 1))).det) ∂(volume : Measure (Eucl n)) = ∫⁻ y, ∑' x : {x : Eucl n // x ∈ D ∧ u x = y}, w x ∂(μHE[n] : Measure (Eucl Q))`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.fiber_sum_glue-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
