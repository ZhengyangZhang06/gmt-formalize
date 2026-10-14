# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.piece_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-aeca31a7f0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1`
- Child key: `piece_mass`
- Declaration: `Submission.cmcdt_lpi_cyl_piece_mass`
- Exact Lean type: `(∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N n : ℕ) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (w : Euclid n → ℤ) (c : Euclid n → ℝ) (Gh : Euclid (n + 1) → Euclid (N + 1)) (Ah : Set (Euclid (n + 1))) (wh : Euclid (n + 1) → ℤ), MeasurableSet A → Measurable w → Measurable c → (∀ u ∈ A, DifferentiableAt ℝ G u) → (∀ u ∈ A, 0 ≤ c u ∧ ∀ α : Covector (Euclid N) n, |α (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))| ≤ c u * covectorEuclideanNorm α) → (∀ z, Gh z = WithLp.toLp 2 (Fin.cons (WithLp.ofLp z 0) (WithLp.ofLp (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))))) → Ah = {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} → (∀ z, wh z = w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) → ∀ ω : DifferentialForm (Euclid (N + 1)) (n + 1), (∀ y, covectorEuclideanNorm (ω y) ≤ 1) → ENNReal.ofReal (∫ z in Ah, (wh z : ℝ) * ω (Gh z) (fun a => fderiv ℝ Gh z (EuclideanSpace.single a 1))) ≤ ∫⁻ u in A, ENNReal.ofReal (|(w u : ℝ)| * c u)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.cyl_fubini-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.suspension_map-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.slice_covector_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
