# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1.piece_imrep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-e558b5edaa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1`
- Child key: `piece_imrep`
- Declaration: `Submission.dimred_mbl_pfi_bilipschitz_piece_imrep`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (H : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ) (w : Euclid n → ℕ) (ζ : Euclid n → MultiVector P n), IsOpen U → LipschitzWith L H → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖H a - H a'‖) → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → H '' B ⊆ U → Measurable w → (∀ a ∈ B, 1 ≤ w a) → AEStronglyMeasurable ζ (volume.restrict B) → (∀ᵐ a ∂(volume.restrict B), ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ α : Covector (Euclid P) n, ζ a α = s * α (fun j => fderiv ℝ H a (EuclideanSpace.single j (1 : ℝ)))) → ∫⁻ a in B, (w a : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (((fderiv ℝ H a).adjoint ∘L fderiv ℝ H a).det)) ∂volume ≠ ∞ → ∃ R : IMRep U n, R.measure U = ∫⁻ a in B, (w a : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (((fderiv ℝ H a).adjoint ∘L fderiv ℝ H a).det)) ∂volume ∧ ∀ ω : DifferentialForm (Euclid P) n, R.action ω = ∫ a in B, (w a : ℝ) * ζ a (ω (H a)) ∂volume`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.injective_unit_orientation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
