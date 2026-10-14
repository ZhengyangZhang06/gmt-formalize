# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.piece_action-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-2849cb9c10/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1`
- Child key: `piece_action`
- Declaration: `Submission.cmcdt_lpi_cyl_piece_action`
- Exact Lean type: `∀ (N n : ℕ) (L : NNReal) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (w : Euclid n → ℤ) (Gh : Euclid (n + 1) → Euclid (N + 1)) (Ah : Set (Euclid (n + 1))) (wh : Euclid (n + 1) → ℤ), LipschitzWith L G → MeasurableSet A → Measurable w → IntegrableOn (fun u => (w u : ℝ)) A → (∀ u ∈ A, DifferentiableAt ℝ G u) → (∀ z, Gh z = WithLp.toLp 2 (Fin.cons (WithLp.ofLp z 0) (WithLp.ofLp (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))))) → Ah = {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} → (∀ z, wh z = w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) → LipschitzWith (max 1 L) Gh ∧ MeasurableSet Ah ∧ Measurable wh ∧ IntegrableOn (fun z => (wh z : ℝ)) Ah ∧ ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (n + 1)) (η : DifferentialForm (Euclid N) n), (∀ (x : Euclid N) (v : Fin n → Euclid N), η x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (n + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∫ u in A, (w u : ℝ) * η (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) = ∫ z in Ah, (wh z : ℝ) * (ω : DifferentialForm (Euclid (N + 1)) (n + 1)) (Gh z) (fun a => fderiv ℝ Gh z (EuclideanSpace.single a 1))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.cyl_fubini-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.suspension_map-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.pullback_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
