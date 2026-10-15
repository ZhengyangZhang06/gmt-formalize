# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1.param_series-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-ca22f1b374/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1`
- Child key: `param_series`
- Declaration: `Submission.dimred_mbl_pfi_param_series_imrep`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (H : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (w : ℕ → Euclid n → ℕ) (ζ : ℕ → Euclid n → MultiVector P n), IsOpen U → (∀ i, ∃ L : NNReal, LipschitzWith L (H i)) → (∀ i, MeasurableSet (B i)) → (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (H i) a) → (∀ i, H i '' B i ⊆ U) → (∀ i, Measurable (w i)) → (∀ i, AEStronglyMeasurable (ζ i) (volume.restrict (B i))) → (∀ i, ∀ᵐ a ∂(volume.restrict (B i)), ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ α : Covector (Euclid P) n, ζ i a α = s * α (fun j => fderiv ℝ (H i) a (EuclideanSpace.single j (1 : ℝ)))) → ∑' i, ∫⁻ a in B i, (w i a : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (((fderiv ℝ (H i) a).adjoint ∘L fderiv ℝ (H i) a).det)) ∂volume ≠ ∞ → ∃ R : IMRep U n, ∀ ω : TestFormOn U n, HasSum (fun i => ∫ a in B i, (w i a : ℝ) * ζ i a ((ω : DifferentialForm (Euclid P) n) (H i a)) ∂volume) (R.action (ω : DifferentialForm (Euclid P) n))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1.bilip_partition-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1.piece_imrep-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1.imrep_tsum-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1.jac_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
