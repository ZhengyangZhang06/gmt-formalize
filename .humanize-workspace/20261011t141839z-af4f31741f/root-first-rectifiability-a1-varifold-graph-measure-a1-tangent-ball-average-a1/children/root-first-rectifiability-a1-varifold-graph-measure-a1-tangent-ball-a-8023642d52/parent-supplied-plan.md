# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.product_blowup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-tangent-ball-a-8023642d52/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1`
- Child key: `product_blowup`
- Declaration: `Submission.frt_vgm_tba_product_blowup_tendsto`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ (g : C_c(Euclidean N, ℝ)) (β : C(Grassmannian N n, ℝ)), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z.1 - x)) * β z.2 ∂V.measure) (𝓝[>] 0) (𝓝 (θ * (β T * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n])))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
