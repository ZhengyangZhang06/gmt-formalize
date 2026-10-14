# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.translate_test-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof step 1: the identity ψ(x) − ψ(x − w) = ∫_0^1 ⟨∇ψ(x − tw), w⟩ dt = div_x((∫_0^1 ψ(x − tw) dt) w), and the application of the hypothesis to the field divided by its sup-norm bound. Here it is used for a single translation vector w, with the t-integral taken outside the divergence: d/dt ∫_F φ(z + tw) dz = −|w|·∫_F div G_t for the elementary fields G_t below, so no parametric vector field has to be differentiated. Notation: B_r := B_r(0), |·| the Euclidean norm, Dφ the derivative.

1. Applying the hypothesis to g = 0 (C¹, compact support, empty tsupport, |g| ≤ 1, div g = 0) gives 0 ≤ C. If w = 0 the left side is ∫_F 0 = 0 = |w|·C. From now on w ≠ 0, so |w| > 0.
2. (Elementary fields.) For t ∈ [0, 1] let G_t(z) := (−|w|⁻¹ φ(z + tw))·w.
 (a) G_t is C¹ (composition/product of C¹ maps), with DG_t(z)h = −|w|⁻¹ Dφ(z + tw)[h]·w. This is the rank-one map h ↦ a(h)·w with the linear form a := −|w|⁻¹ Dφ(z + tw), whose trace is a(w). Hence div G_t(z) = −|w|⁻¹ Dφ(z + tw)[w].
 (b) If G_t(z) ≠ 0 then φ(z + tw) ≠ 0. So tsupport G_t ⊆ tsupport(φ(· + tw)) = {z : z + tw ∈ tsupport φ} = tsupport φ − tw, a compact set (translation is a homeomorphism); hence G_t has compact support.
 (c) For z in that set, z + tw ∈ tsupport φ ⊆ B_R, so |z| ≤ |z + tw| + t|w| < R + |w| (as 0 ≤ t ≤ 1). Thus tsupport G_t ⊆ B_{R+|w|}.
 (d) |G_t(z)| = |w|⁻¹·|φ(z + tw)|·|w| = |φ(z + tw)| ≤ 1.
 By the hypothesis, ∫_F −|w|⁻¹ Dφ(z + tw)[w] dz ≤ C; multiplying by |w| > 0:
 (∗) ∫_F Dφ(z + tw)[w] dz ≥ −|w|·C for every t ∈ [0, 1].
3. (Differentiation under the integral sign.) Let Φ(t) := ∫_F φ(z + tw) dz for t ∈ ℝ. Dφ is continuous with compact support (tsupport Dφ ⊆ tsupport φ), so |Dφ| ≤ B for some B. Fix t₀ ∈ ℝ. For |t − t₀| < 1 the t-derivative of the integrand, Dφ(z + tw)[w] (chain rule), satisfies |Dφ(z + tw)[w]| ≤ B|w| and vanishes unless z + tw ∈ tsupport φ ⊆ B_R, which forces |z| < R + |t||w| ≤ R + (|t₀| + 1)|w|. Hence it is dominated by B|w|·1_{closedBall(0, R+(|t₀|+1)|w|)}(z), which is integrable on F. The integrands are continuous in z (so measurable), z ↦ φ(z + t₀w) is integrable (continuous, compact support), and z ↦ Dφ(z + t₀w)[w] is continuous. By the dominated differentiation theorem, Φ is differentiable at t₀ with Φ'(t₀) = ∫_F Dφ(z + t₀w)[w] dz.
4. Ψ(t) := Φ(t) + |w|·C·t is differentiable on ℝ with Ψ'(t) = Φ'(t) + |w|·C, which is ≥ 0 for t ∈ (0, 1) by (∗). Ψ is continuous on [0, 1] and differentiable in its interior with nonnegative derivative, so Ψ is monotone on [0, 1]; in particular Ψ(0) ≤ Ψ(1), i.e. Φ(0) − Φ(1) ≤ |w|·C.
5. φ and φ(· + w) are continuous with compact support, hence integrable on F, so Φ(0) − Φ(1) = ∫_F φ(z) dz − ∫_F φ(z + w) dz = ∫_F (φ(z) − φ(z + w)) dz. Together with 4 this is the claim. ∎

Formalization notes: HasFDerivAt.comp with (hasFDerivAt_id z).add_const, HasFDerivAt.const_mul, HasFDerivAt.smul_const (fderiv G_t z = (c • fderiv ℝ φ (z + t • w)).smulRight w with c = −‖w‖⁻¹); identify the coerced linear map with ((c • fderiv ℝ φ (z + t • w)) : E →ₗ[ℝ] ℝ).smulRight w by `ext; simp`, then LinearMap.trace_smulRight; tsupport_smul_subset_left, tsupport_mul_subset_right, tsupport_comp_eq_preimage φ (Homeomorph.addRight (t • w)), HasCompactSupport.comp_homeomorph, .mul_left, .smul_right; tsupport_fderiv_subset, (hφc.fderiv ℝ).exists_bound_of_continuous; hasDerivAt_integral_of_dominated_loc_of_deriv_le with s := ball t₀ 1 (first argument ball_mem_nhds t₀ zero_lt_one); monotoneOn_of_deriv_nonneg on convex_Icc 0 1 with interior_Icc; Integrable.comp_add_right, integral_sub. Do not `set E := Euclid n` (it shadows the hypotheses' types); use `exact` rather than `simpa` where `φ ∘ (· + t • w)` must match `fun y => φ (y + t • w)`. Optional formalization aid: a complete machine-checked Lean proof of exactly this frozen statement (compiled after `import GMT.Ch07.Submission` in namespace GMT.Ch07 with the contract opens; sibling results are used by their `Submission.*` names) is the theorem at line 173 of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a7cdf67795/bvc-split-lean-prototype.lean.txt (sha256 bd274b1c5aaf00c2d9facbece96054908343f66e3321434d45377655689496b8). The numbered proof above is self-contained.

## Key steps

1. C ≥ 0 (g = 0); trivial if w = 0.
2. For t ∈ [0,1], G_t = −|w|⁻¹ φ(·+tw) w is admissible with div G_t = −|w|⁻¹ Dφ(·+tw)[w], so ∫_F Dφ(z+tw)[w] ≥ −|w|C.
3. Φ(t) = ∫_F φ(z+tw) is differentiable with Φ'(t) = ∫_F Dφ(z+tw)[w] (dominated differentiation).
4. Ψ(t) = Φ(t) + |w|Ct is monotone on [0,1], so ∫_F (φ − φ(·+w)) = Φ(0) − Φ(1) ≤ |w|C.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg in snapshot mathlib: 'theorem ae_convolution_tendsto_right_of_locallyIntegrable', 'contDiff_convolution_left', 'theorem support_normed_eq', 'integral_normed', 'trace_smulRight', 'theorem extraction_forall_of_frequently', 'frequently_atTop_iff_infinite', 'uniformContinuous_of_continuous', 'theorem integral_integral_swap', 'integral_sub_left_eq_self|integral_add_right_eq_self', 'finite_cover_balls', 'ContDiff.lipschitzWith_of_hasCompactSupport', 'theorem Integrable.bdd_mul|theorem Integrable.mul_bdd', 'setIntegral_mono_on|integral_mono_of_nonneg', 'integral_prod_right', 'exists_contDiff_support_eq_eq_one_iff|exists_isOpen_lt_add|tendsto_measure_cthickening|exists_isCompact_diff_lt', 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le'`
- `lake env lean /tmp/bvc-split-check/Avail.lean and Avail2.lean: #check of about 70 lemma names after import GMT.Ch07.Submission to determine the frozen import closure`
- `python3 scans of dag.json (979 nodes): depth/status of the selected node; accepted statements mentioning StrictMono, Finset ℕ, indicator, symmDiff, Lipschitz; exact-type comparison of dorag_ha_rb_sup_net, dgcr_stc_exists_normalized_mollifier, cmc_fc_cs_diagonal_subseq; collision check of the 9 new codim1_rdo_dg_bvc_* names; cross-parent reuse count; proof sizes of accepted depth-6 leaves`
- `git show 043dcc28e6f06fdf02b550a807c0573e295fc4d9 / b046f226689afca88f2ceb966c9010ac5e581de0 / 376e5f482d73f6f48d00a4945533b15f784859d5 :GMT/Ch07/Submission.lean (accepted proofs to be reused)`
- `sed -n 560,640p book/chapter-02.txt (Simon 2.6 statement and printed proof)`
- `grep runtime.py (_decompose depth guard, _existing_lean_name_problem, _accepted_checkpoint, _solve_children reuse, _install_parent_supplied_child_handoff), prompts.py ('Preserve the exact target, hypotheses, imports'), verifier gmt-compare.py (candidate_inputs, dot-directory skipping)`
- `lake env lean -DautoImplicit=false /tmp/bvc-split-check/{Types,Glue3,Glue4,Glue6,LeafA,LeafAB,LeafC,LeafF,LeafJL,All,Full}.lean; final Full.lean: exit 0, 0 errors, 0 sorry, #print axioms Submission.codim1_rdo_dg_bv_set_compactness`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Cofinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a7cdf67795/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a7cdf67795/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a7cdf67795/bvc-split-lean-prototype.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/prompts.py`
- `/tmp/bvc-split-check/Types.lean`
- `/tmp/bvc-split-check/Avail.lean`
- `/tmp/bvc-split-check/Avail2.lean`
- `/tmp/bvc-split-check/Full.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) equals workspace HEAD and .lake/packages/mathlib; simongmt is 2b366308; snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). No local declaration states BV/perimeter compactness, the L¹ duality on balls, or the translation/mollification estimates ('bvc' has 0 hits in dag.json and SimonGMT). Three accepted theorems have exactly the needed types and are reused by name: Submission.dorag_ha_rb_sup_net (043dcc28), Submission.dgcr_stc_exists_normalized_mollifier (376e5f48), Submission.cmc_fc_cs_diagonal_subseq (b046f226). Import closure of GMT.Ch07.Submission (imports are frozen): absent are ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, ContDiffBump.convolution_tendsto_right, Integrable.exists_hasCompactSupport_integral_sub_le, Lp.boundedContinuousFunction_dense and exists_smooth_zero_one_of_isClosed. Present are exists_contDiff_support_eq_eq_one_iff (Geometry/Manifold/PartitionOfUnity.lean:789), MeasurableSet.exists_isCompact_isClosed_sdiff_lt and IsCompact.exists_isOpen_lt_add (Measure/Regular.lean:930), hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286), ContDiff.lipschitzWith_of_hasCompactSupport (ContDiff/RCLike.lean:156), LinearMap.trace_smulRight (LinearAlgebra/Trace.lean:272), integral_integral_swap (Integral/Prod.lean:478), integral_sub_left_eq_self/integral_add_right_eq_self, Filter.extraction_forall_of_frequently (AtTopBot/Basic.lean:123), ENNReal.tsum_geometric, and Integrable.bdd_mul/mul_bdd (L1Space/Integrable.lean:1067). Hence the duality child uses regularity plus smooth Urysohn rather than a.e. convergence of mollifiers. Simon 2.6's printed proof delegates precompactness to [GT01, 7.22], so the parent proof is a composed argument that the children specialize. Lean: all 12 child types elaborate, and the 864-line prototype proving every child and the parent's exact frozen type compiles (exit 0, no sorry; axioms propext, Classical.choice, Quot.sound).
