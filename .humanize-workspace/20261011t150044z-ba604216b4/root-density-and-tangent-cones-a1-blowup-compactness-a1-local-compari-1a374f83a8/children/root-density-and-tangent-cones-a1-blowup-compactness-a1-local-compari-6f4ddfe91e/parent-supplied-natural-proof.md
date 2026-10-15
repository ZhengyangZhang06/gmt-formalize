# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.grad_weak_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of dtc_bc_lc_sl_lipschitz_leibniz, step 4(d) ("Euclidean weak-* convergence"). That step makes precise Simon's parenthetical remark in the proof of Ch. 6, Lemma 4.5(2) (chapter-06.txt lines 1256–1261, printed p. 156), that (1) "follows fairly easily by approximating v by smooth functions and using the fact that h^{(σ)} converges to h uniformly". Here the argument is stated for arbitrary uniformly convergent, uniformly Lipschitz functions on ℝ^N. The parent applies it, via piece_weak_limit, to u_k = h_k∘ψ̃ and u = h∘ψ̃ on a chart.

Imports. Add `import Mathlib.MeasureTheory.Function.ContinuousMapDense` and `import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox` to GMT/Ch07/Submission.lean. Accepted candidates already do this, e.g. dtc_mass_eq_measure. Rademacher's theorem (Mathlib.Analysis.Calculus.Rademacher) is already in the import closure.

Notation. ℝ^N = Euclid N, L^N = volume. e_1, …, e_N is the standard basis (EuclideanSpace.single i 1). For Z : ℝ^N → ℝ^N write Z_i(y) := Z(y) i, so Z(y) = Σ_i Z_i(y)e_i. For a function f : ℝ^N → ℝ, Df(y) := fderiv ℝ f y, which is 0 where f is not differentiable. For integrable Z put I_f(Z) := ∫ Df(y)(Z(y)) dy.

1. Bounds and linearity. Let f be Λ-Lipschitz. Then ‖Df(y)‖ ≤ Λ for every y (norm_fderiv_le_of_lipschitz). The map y ↦ Df(y) is Borel (measurable_fderiv). Evaluation (L, z) ↦ L z is continuous. Hence for every integrable Z the function y ↦ Df(y)(Z(y)) is a.e.-strongly measurable and bounded by Λ|Z(y)|, so it is integrable. Consequently I_f is additive on integrable fields, and for integrable Z, Z':
 |I_f(Z) − I_f(Z')| = |I_f(Z − Z')| ≤ Λ ∫ |Z − Z'| dy.

2. Integration by parts against smooth fields. Let Φ : ℝ^N → ℝ^N be C^∞ with compact support.
 - Each Φ_i is C^∞ with compact support, hence Lipschitz (ContDiff.lipschitzWith_of_hasCompactSupport (hf : HasCompactSupport f) (h'f : ContDiff ℝ n f) (hn : n ≠ 0)).
 - ∂_iΦ_i(y) := DΦ_i(y)e_i is continuous with compact support.
 Let f be Λ-Lipschitz. By Rademacher (LipschitzWith.ae_differentiableAt), f is differentiable at a.e. y, and there lineDeriv ℝ f y e_i = Df(y)e_i (DifferentiableAt.lineDeriv_eq_fderiv). Mathlib's integration by parts for Lipschitz functions (LipschitzWith.integral_lineDeriv_mul_eq, with μ = volume, f, g := Φ_i, v := e_i) gives
 ∫ lineDeriv ℝ f y e_i · Φ_i(y) dy = ∫ lineDeriv ℝ Φ_i y (−e_i) · f(y) dy = −∫ ∂_iΦ_i(y) f(y) dy.
 The last equality holds because Φ_i is differentiable, so lineDeriv ℝ Φ_i y (−e_i) = DΦ_i(y)(−e_i) = −∂_iΦ_i(y).
 Since Df(y)(Φ(y)) = Σ_i Φ_i(y)Df(y)e_i, this gives
 I_f(Φ) = Σ_i ∫ Df(y)e_i Φ_i(y) dy = −Σ_i ∫ ∂_iΦ_i(y) f(y) dy.
 All integrands are integrable: each is a bounded measurable function times a continuous compactly supported one, or a continuous function times a continuous compactly supported one.

3. Convergence against smooth fields. Put δ_k := sup_y |u_k(y) − u(y)|. By uniform convergence δ_k is finite for large k and δ_k → 0. For such k,
 |∫ ∂_iΦ_i u_k dy − ∫ ∂_iΦ_i u dy| ≤ δ_k ∫ |∂_iΦ_i| dy → 0.
 Step 2, applied to f = u_k and to f = u, gives I_{u_k}(Φ) → I_u(Φ).

4. Smooth compactly supported approximation of W. Let δ > 0.
 (a) By MeasureTheory.Integrable.exists_hasCompactSupport_integral_sub_le (ContinuousMapDense; its [μ.Regular] instance resolves for volume on Euclid N), there is a continuous, compactly supported Φ₀ : ℝ^N → ℝ^N with ∫ |W − Φ₀| dy ≤ δ/2.
 (b) Choose R > 0 with tsupport Φ₀ ⊆ closedBall(0, R). Let χ be the smooth bump ContDiffBump centred at 0 with rIn = R and rOut = 2R. Then 0 ≤ χ ≤ 1, χ = 1 on closedBall(0, R), and χ = 0 off B_{2R}(0). Put η := δ/(2(L^N(closedBall(0, 2R)) + 1)) > 0. Φ₀ is uniformly continuous, being continuous with compact support. By UniformContinuous.exists_contDiff_dist_le (SmoothApprox) there is a C^∞ map g with |g(y) − Φ₀(y)| < η for every y.
 (c) Put Φ := χ·g. Φ is C^∞ with compact support. Since χΦ₀ = Φ₀, we have Φ − Φ₀ = χ(g − Φ₀). Hence |Φ − Φ₀| ≤ η·1_{closedBall(0,2R)} and ∫ |Φ − Φ₀| dy ≤ η·L^N(closedBall(0, 2R)) ≤ δ/2.
 Therefore ∫ |W − Φ| dy ≤ δ.

5. Conclusion. Fix δ > 0 and the Φ of step 4.
 - By step 1, |I_{u_k}(W) − I_{u_k}(Φ)| ≤ Λδ for every k, and |I_u(W) − I_u(Φ)| ≤ Λδ.
 - By step 3 there is k₀ with |I_{u_k}(Φ) − I_u(Φ)| ≤ δ for k ≥ k₀.
 Hence |I_{u_k}(W) − I_u(W)| ≤ (2Λ + 1)δ for all k ≥ k₀. As δ > 0 was arbitrary, ∫ Du_k(y)(W(y)) dy → ∫ Du(y)(W(y)) dy. ∎

## Key steps

1. Lipschitz bounds: ‖Df‖ ≤ Λ, so W ↦ ∫ Df(W) is linear and Λ-Lipschitz in L¹.
2. Integration by parts for Lipschitz functions (LipschitzWith.integral_lineDeriv_mul_eq): ∫ Df(Φ) = −Σ_i ∫ ∂_iΦ_i f for C^∞ compactly supported Φ.
3. Uniform convergence u_k → u gives ∫ Du_k(Φ) → ∫ Du(Φ) for such Φ.
4. L¹-density of C^∞ compactly supported fields (ContinuousMapDense, then SmoothApprox and a bump cut-off).
5. ε/3 argument: limsup |∫ Du_k(W) − ∫ Du(W)| ≤ (2Λ + 1)δ for every δ > 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 -I scans of dag.json: the slicing-a1 children (chart_pieces, coarea, slice_family, ...) and their lean_statements; the dependencies im_calculus, defect_identity, lipschitz_smoothing, chart_pieces; regex 'lipschitz_leibniz|leibniz|tangential gradient|weak convergence|chart gradient' and 'TendstoUniformly|integral_lineDeriv|weak-limit|weakly' (hits dor_lmbsf_lipschitz_cutoff_leibniz, dor_lmbsf_piece_weak_limit, dor_lmbsf_tangential_gradient: all decomposing, different statements)`
- `git show <accepted commit>:GMT/Ch07/Submission.lean and whitespace-normalised comparison of theorem Submission.<name> with the DAG type: cmc_imRep_locality_restrict_sub (2af75d6), cmcs_cd_defect_identity (e32f0ad), cmcs_lipschitz_smoothing (00c458d) -> IDENTICAL`
- `grep -c dtc_bc_lc_sl_ll_ dag.json (0); git log --all -S dtc_bc_lc_sl_ll_ (no match); grep -rl dtc_bc_lc_sl_ll_ runs/.../nodes (none)`
- `scan of the 958 accepted candidate commits for imports added to Submission.lean (26 do, e.g. Poincare.SimonGMT.Chapter02.WeightedArea, Chapter02.AreaLipschitz, Mathlib.MeasureTheory.Function.ContinuousMapDense, Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox); verifier/gmt-compare.py candidate_inputs/child_modules/contract_scope (Submission.lean and new GMT/Ch07 files may change)`
- `grep in the snapshot mathlib for integral_lineDeriv_mul_eq, ae_differentiableAt_of_real, Besicovitch.ae_tendsto_measure_inter_div, Integrable.exists_hasCompactSupport_integral_sub_le, UniformContinuous.exists_contDiff_dist_le, tendsto_tsum_of_dominated_convergence, integral_iUnion, hasSum_integral_iUnion, setIntegral_congr_set, MeasurableSet.image_of_continuousOn_injOn, euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, alternatizeUncurryFinCLM, alternatizeUncurryFin_apply, smulRightL, ContDiff.lipschitzWith_of_hasCompactSupport, ContDiffBump.one_of_mem_closedBall`
- `grep in SimonGMT for HasApproximateTangentSpaceAt (definition, .unique, support_euclideanHausdorffMeasure_restrict_submodule, regular_euclideanHausdorffMeasure_restrict_submodule), weighted_area_formula_volume_of_injective_derivative, integral_area_formula_of_injective_derivative, injective_area_formula_areaJacobianAt, integrableOn_image_iff_integrableOn_areaJacobian_smul, areaJacobianAt_eq_zero_iff_not_injective, ae_eq_of_hasFDerivWithinAt, ae_fderivWithin_eq_of_lipschitz_extension, continuous_normDet, measurable_areaJacobianAt`
- `lake env lean on /tmp/llz_dec/AllTypes.lean (11 types in the contract-mode challenge header), Avail.lean, Avail2.lean and Avail3.lean (#check of every cited lemma with the base and the extra imports), and AssemblyAll.lean with #print axioms`
- `sed book/chapter-06.txt lines 1180–1300 (4.2–4.5 and the proof of 4.5(2), including (1)–(3)); book/chapter-03.txt lines 325–362 (Definition 2.1 and the remark that ∇^M f does not depend on the decomposition)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-1a374f83a8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/llz_dec/AllTypes.lean`
- `/tmp/llz_dec/AssemblyAll.lean`

The pinned libraries supply the tools but none of the needed lemmas. SimonGMT has Simon's approximate tangent spaces with uniqueness and plane-support lemmas (Ch. 3), the injective weighted, Bochner and measure area formulas with Jacobian positivity, and a.e. uniqueness of within-derivatives (Ch. 2, AreaDomain). Mathlib has Rademacher, integration by parts for Lipschitz functions, L¹-density of C_c functions, smooth uniform approximation, Tannery's theorem, Lusin–Souslin and the μHE scaling and translation laws. No pinned or DAG declaration proves any of: uniqueness of approximate differentials along a set, weak-* convergence of gradients, the anti-Lipschitz bound for immersions, the chart pull-back, or the Leibniz rule with a Lipschitz multiplier. The dor_lmbsf_* analogues are decomposing and state different results. Hence there are nine new children, with the prefix dtc_bc_lc_sl_ll_ (absent from dag.json and git history), plus two accepted declarations reused with identical types: cmc_imRep_locality_restrict_sub (2af75d6) and cmcs_cd_defect_identity (e32f0ad). Four children need imports outside the base closure: ContinuousMapDense, SmoothApprox, Chapter02.WeightedArea/AreaCritical, Chapter02.AreaDomain and Tannery. Accepted candidates already add such imports. All 11 types elaborate in the contract-mode challenge header. Lean assemblies prove the parent type from weak_limit, smooth_leibniz, orient_interior, chart_pieces and lipschitz_smoothing, and prove weak_limit, piece_gradient, piece_weak_limit and smooth_leibniz from their declared dependencies, all with axioms propext, Classical.choice and Quot.sound only.
