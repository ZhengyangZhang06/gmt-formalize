# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.density_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent basic fact (F9) (parent step 2(iii); Simon Ch. 3, Remark 1.8(2) and Theorem 1.9: for a countably n-rectifiable H^n-measurable M and locally H^n-integrable θ, Θ^n(θH^n⌞M, x) = θ(x) for H^n-a.e. x ∈ M and = 0 for H^n-a.e. x ∉ M).
Notation: Hⁿ := μHE[n]; M := R.carrier, θ := R.mult (ℕ-valued), μ := R.measure = (Hⁿ.restrict M).withDensity(x ↦ (θ x : [0, ∞])); g(x) := Set.indicator M (y ↦ (θ y : [0, ∞])) x; r(x, ρ) := μ(B_ρ(x))/(unitBallVolume n·ofReal(ρ^n)); L(x) := limsup_{ρ→0⁺} r(x, ρ) ∈ [0, ∞].
1. (DEM) applied to P, n, U, R (n ≥ 1 and μ(K) ≠ ∞ for compact K are our hypotheses) gives: for Hⁿ-a.e. x, r(x, ·) → g(x) along 𝓝[>]0.
2. Fix x at which this convergence holds. The filter 𝓝[>]0 on ℝ is not the bottom filter (NeBot instance for nhdsWithin of Ioi), so the limsup of a convergent function is its limit (Filter.Tendsto.limsup_eq): L(x) = g(x). Since g(x) is either 0 or the coercion of the natural number θ(x), g(x) ≠ ∞, hence ofReal(L(x).toReal) = L(x) = g(x) (ENNReal.ofReal_toReal).
3. By steps 1–2, (x ↦ ofReal(L(x).toReal)) =ᵐ[Hⁿ] g (Filter.Eventually.mono). Hence Hⁿ.withDensity(x ↦ ofReal(L(x).toReal)) = Hⁿ.withDensity g (withDensity_congr_ae; no measurability of the integrand is required).
4. M is measurable (IMRep.measurableSet_carrier), so Hⁿ.withDensity(Set.indicator M (y ↦ θ y)) = (Hⁿ.restrict M).withDensity(y ↦ θ y) (withDensity_indicator), which is μ by the definition of IMRep.measure.
5. Steps 3 and 4 give μ = Hⁿ.withDensity(x ↦ ofReal(L(x).toReal)); the integrand is literally fun x => ENNReal.ofReal ((limsup (fun ρ => R.measure (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal). ∎

## Key steps

1. (DEM) gives, for Hⁿ-a.e. x, convergence of the density ratio to the finite value 1_M(x)θ(x).
2. Where the ratio converges, limsup = limit along the nontrivial filter 𝓝[>]0, and ofReal ∘ toReal is the identity on finite values.
3. withDensity_congr_ae and withDensity_indicator identify Hⁿ.withDensity(ofReal ∘ d) with (Hⁿ⌞M).withDensity θ = R.measure.

## Reference use

### local-project

Queries:
- `python3 -I -c json.load(local-references/123e8435b4a2469b/manifest.json); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `python3 scan of dag.json lean_statement fields for 'BoundaryVanishes (blowUp', 'blowUp', 'restrict', 'withDensity', 'map (dilation', 'IsEmbeddedSubmanifold 2 (n + k) univ', 'HasCompactSupport f → ∫', with status, candidate_commit and depends_on of each match`
- `python3 extraction of subproblem.lean_statement/natural_proof/proof_key_steps from the parent-child-handoff.json of the six reused accepted nodes; isolated-comparator-result.json of borel-restriction-a1 and of blowup_limit_cycle (node dir ...-34a94daa02)`
- `grep -n '^theorem|^def|^structure|^instance' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,AffineCurrentPushforward,Mass}.lean; sed -n 20,120p Chapter03/Rectifiable.lean`
- `grep -rn 'ext_of_integral_eq_on_compactlySupported|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts|theorem restrict_map|measure_null_of_locally_null|extraction_of_frequently_atTop|IsCompact.tendsto_subseq|continuous_of_dominated|tendsto_integral_filter_of_dominated_convergence|euclideanHausdorffMeasure_smul₀|ext_of_forall_integral_eq' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -c 'idtp_fons_cc_\|idtp_fcc_' dag.json; grep -rl nodes/; grep -rl --include=Submission.lean ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/; git log --all -S idtp_fons_cc_ (all empty)`
- `sed -n 300,330p and 420,535p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt (Simon 7.3.1 and the proof of 7.3.3)`
- `lake env lean /tmp/ccd_k7q2/final/Types.lean; lake env lean /tmp/ccd_k7q2/final/AssemblyAx.lean (#print axioms); lake env lean /tmp/ccd_k7q2/final/AC.lean, DR.lean, CR.lean, TMB.lean`
- `python3 replay of Runtime._dependency_problem, Runtime._topological and Runtime._existing_lean_name_problem on /tmp/ccd_k7q2/final/subproblems_final.json against dag.json (updated_at 2026-10-13T19:24:44Z)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5982ed9bb9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-34a94daa02/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-34a94daa02/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-borel-restriction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-borel-restriction-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invaria-4622bb5be6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/ccd_k7q2/final/Types.lean`
- `/tmp/ccd_k7q2/final/AssemblyAx.lean`
- `/tmp/ccd_k7q2/final/AC.lean`
- `/tmp/ccd_k7q2/final/DR.lean`
- `/tmp/ccd_k7q2/final/CR.lean`
- `/tmp/ccd_k7q2/final/TMB.lean`

Pins match: manifest project b4d606db1 = workspace HEAD, Mathlib 25730c7c; SimonGMT 2b36630; the snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Reusable accepted declarations (dag.json; candidate commits present locally; isolated comparator passed): dimred_im_mass_measure (01ae2c59), dtc_blowUp_scaling (a94d596c), cone_current_imrep_measure_smul_image (e183b985), idtp_tpf_blowUp_limit_boundaryVanishes (f498a8ef; exactly the parent's (F7)), dor_lmb_imrep_restrict_current (90d679af; Borel restriction of an IMRep with weight μ⌞A, used for 3(h)) and dimred_cs_mi_withDensity_dilate (fc55b748; n-homogeneity of Hⁿ.withDensity f, used for step 14). Their types are copied byte for byte. No accepted or library declaration states the ambient-submanifold fact, the dilation calculus of rescaled measures, (F9) from DEM, the monotonicity consequences, the tangent-measure statement or the positive-scale family, so these enter as the six fresh children (fresh idtp_fons_cc_ names occur nowhere). Library facts used in the child proofs: SimonGMT GeometricCurrentOn.boundary_affinePushforward (Chapter06/AffineCurrentPushforward.lean:188), restrictDomain_apply, zeroRegion and support (CurrentLocalEquality.lean), massOn (Mass.lean:68), countablyRectifiable_of_measure_zero (Chapter03/Rectifiable.lean:45). Snapshot Mathlib: Measure.ext_of_integral_eq_on_compactlySupported (RieszMarkovKakutani/Real.lean:412), Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (Measure/Regular.lean:1183), MeasurableEmbedding.restrict_map (Measure/Restrict.lean:890), measure_null_of_locally_null (OuterMeasure/Basic.lean:150), extraction_of_frequently_atTop (AtTopBot/Basic.lean:114), IsCompact.tendsto_subseq (Topology/Sequences.lean:298), tendsto_integral_filter_of_dominated_convergence, euclideanHausdorffMeasure_smul₀ (Euclidean/Volume/Measure.lean:152). Lean: all 12 types elaborate. The parent's frozen type compiles from the child types (stated as axioms) and uses exactly the six new children plus dimred_im_mass_measure, dtc_blowUp_scaling, dor_lmb_imrep_restrict_current and the standard axioms. ambient_calculus and density_representation are fully proved; cycle_rescale is proved from its siblings' frozen types; tangent_measures (B) is derived from (A). The runtime replay accepts the split.
