# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.piece_tangent-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.piece_tangent-a1.rescaled_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 2 (coercivity), 4 (localization) and 5 (convergence) of the parent proof. Hypothesis (iii) is the conclusion of the parent's step 5(i) for every radius; the parent's assembly gets it from the sibling lebesgue_points applied to g₀ = 1_B·J at points b ∈ B, where g₀(b) = J(b). The uniform convergence of the difference quotients in step 5(ii) is the sibling diff_quotient_uniform. Departures (cosmetic): the coercivity constant is used in the anti-Lipschitz form |c| ≤ κ|Λc|; the radius is ρ := R₁/m + κR₁ + 1 instead of max(R/m, R/κ); and the limit is proved by an explicit ε-estimate. The point b need not lie in B.

Notation. g₀ := 1_B·J = B.indicator J. Φ_r(c) := r^{-1}(F(b + rc) − F(b)). u_r(c) := g₀(b + rc)·f(Φ_r(c)), the integrand on the left. v(c) := J(b)·f(Λc).

1. (Coercivity; parent step 2.) Λ is an injective linear map on the finite-dimensional space ℝ^n, so ker Λ = 0. LinearMap.exists_antilipschitzWith gives κ > 0 with Λ κ-anti-Lipschitz. Then ContinuousLinearMap.bound_of_antilipschitz gives |c| ≤ κ·|Λc| for every c ∈ ℝ^n.
2. (Support radius and bound of f.) tsupport f is compact, hence bounded, so tsupport f ⊆ closedBall(0, R₀) for some R₀ (IsCompact.isBounded, Bornology.IsBounded.subset_closedBall). Put R₁ := max(R₀, 0) ≥ 0. If |y| > R₁ then y ∉ tsupport f, so f(y) = 0 (image_eq_zero_of_notMem_tsupport). f is continuous with compact support, hence bounded: there is M with |f(y)| ≤ M for all y (Continuous.bounded_above_of_compact_support). Then M ≥ |f(0)| ≥ 0.
3. (Localization; parent step 4.) Put ρ := R₁/m + κR₁ + 1 > 0 and D := closedBall(0, ρ) ⊆ ℝ^n. Let r > 0 and c ∉ D, i.e. |c| > ρ.
(a) u_r(c) = 0. If b + rc ∉ B, then g₀(b + rc) = 0. If b + rc ∈ B, hypothesis (i) with a = b + rc gives m·r|c| = m|(b + rc) − b| ≤ |F(b + rc) − F(b)|. Since κR₁ ≥ 0, |c| > ρ > R₁/m, so R₁ < m|c|. Then R₁ < m|c| = r^{-1}·(m·r|c|) ≤ r^{-1}|F(b + rc) − F(b)| = |Φ_r(c)|, so f(Φ_r(c)) = 0 by step 2.
(b) v(c) = 0. Suppose |Λc| ≤ R₁. Then |c| ≤ κ|Λc| ≤ κR₁ ≤ R₁/m + κR₁ < ρ by step 1, a contradiction. So |Λc| > R₁ and f(Λc) = 0 by step 2.
4. (Measurability, bounds, integrability on D.) λ(D) < ∞ (measure_closedBall_lt_top).
- K ≥ J(b) ≥ 0, and |g₀(a)| ≤ K for every a: g₀(a) = J(a) ∈ [0, K] if a ∈ B, and g₀(a) = 0 otherwise. Also |J(b)| ≤ K.
- g₀ is Borel (Measurable.indicator: J is Borel and B is Borel). So c ↦ g₀(b + rc) is Borel, being g₀ composed with the continuous affine map c ↦ b + rc.
- c ↦ f(Φ_r(c)) and c ↦ f(Λc) are continuous, since F, f and Λ are continuous. (Lean: `fun_prop` proves the first; the measurability of c ↦ |g₀(b + rc) − J(b)| is continuous_abs.measurable.comp of a measurable map.)
- Hence the following are Borel and bounded on ℝ^n: u_r (by KM), v (by KM), c ↦ |g₀(b + rc) − J(b)| (by 2K) and c ↦ |f(Φ_r(c)) − f(Λc)| (by 2M). Each is therefore integrable on D (Measure.integrableOn_of_bounded).
5. (Reduction to D.) For r > 0, ∫ u_r dλ = ∫_D u_r dλ by step 3(a) (setIntegral_eq_integral_of_forall_compl_eq_zero). Likewise J(b)·∫ f(Λc) dλ(c) = ∫ J(b)·f(Λc) dλ(c) = ∫_D v dλ by integral_const_mul and step 3(b).
6. (Pointwise bound; parent step 5.) For every c, u_r(c) − v(c) = (g₀(b + rc) − J(b))·f(Φ_r(c)) + J(b)·(f(Φ_r(c)) − f(Λc)). With |f| ≤ M and |J(b)| ≤ K this gives |u_r(c) − v(c)| ≤ M·|g₀(b + rc) − J(b)| + K·|f(Φ_r(c)) − f(Λc)|.
7. (Uniform convergence; parent step 5(ii).) The sibling diff_quotient_uniform, with k := P, f := F, v := b and R := ρ, says that Φ_r → Λ uniformly on D as r → 0⁺. f is continuous with compact support, hence uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). So f∘Φ_r → f∘Λ uniformly on D (UniformContinuous.comp_tendstoUniformlyOn). By Metric.tendstoUniformlyOn_iff: for every δ > 0, eventually as r → 0⁺, |f(Λc) − f(Φ_r(c))| < δ for all c ∈ D.
8. (ε-estimate.) Let ε > 0 and V := λ(D) ∈ [0, ∞). Put ε₁ := ε/(2(M + 1)) > 0 and ε₂ := ε/(2(K + 1)(V + 1)) > 0. Each of the following holds eventually as r → 0⁺, hence all three hold together:
- r > 0 (self_mem_nhdsWithin);
- A(r) := ∫_D |g₀(b + rc) − J(b)| dλ(c) < ε₁, by hypothesis (iii) with R := ρ > 0 (note A(r) ≥ 0);
- |f(Φ_r(c)) − f(Λc)| < ε₂ for all c ∈ D, by step 7.
Fix such an r. By step 5, the distance from ∫ u_r dλ to J(b)·∫ f∘Λ dλ is |∫_D u_r − ∫_D v| = |∫_D (u_r − v)| (integral_sub, using step 4). Then
|∫_D (u_r − v)| ≤ ∫_D |u_r − v| ≤ ∫_D (M·|g₀(b + rc) − J(b)| + K·|f(Φ_r(c)) − f(Λc)|) dλ(c) = M·A(r) + K·∫_D |f∘Φ_r − f∘Λ| dλ.
The steps are abs_integral_le_integral_abs, setIntegral_mono_on with step 6, and integral_add with integral_const_mul (integrability by step 4). (Lean note: parenthesize as M * (∫ c in D, …) + K * (∫ c in D, …), because the binder of ∫ extends to the right.) Moreover ∫_D |f∘Φ_r − f∘Λ| dλ ≤ ε₂·V by norm_setIntegral_le_of_norm_le_const, as λ(D) < ∞ and the integrand is < ε₂ on D. Hence the distance is at most M·ε₁ + K·ε₂·V. Finally M·ε₁ = (ε/2)·M/(M + 1) < ε/2 since M ≥ 0, and K·ε₂·V = (ε/2)·(K/(K + 1))·(V/(V + 1)) < ε/2 since K, V ≥ 0. So the distance is < ε.
9. (Conclusion.) ε > 0 was arbitrary, so ∫ u_r dλ → J(b)·∫ f(Λc) dλ(c) as r → 0⁺ (Metric.tendsto_nhds). ∎

## Key steps

1. Injectivity of Λ = DF(b) on ℝ^n gives κ > 0 with |c| ≤ κ|Λc|; f vanishes outside closedBall(0, R₁) and |f| ≤ M.
2. With ρ := R₁/m + κR₁ + 1, the co-Lipschitz bound at b and the coercivity of Λ make u_r (r > 0) and v = J(b)·f∘Λ vanish outside D = closedBall(0, ρ).
3. On D, |u_r − v| ≤ M·|1_B J(b + r·) − J(b)| + K·|f∘Φ_r − f∘Λ|, and all four functions are bounded Borel, hence integrable on D.
4. Hypothesis (iii) with R = ρ controls the first term; diff_quotient_uniform plus uniform continuity of f makes f∘Φ_r → f∘Λ uniformly on D, controlling the second; an ε-estimate gives the limit.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; python3 read of <snapshot>/project/lake-manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem LinearMap.exists_antilipschitzWith|theorem bound_of_antilipschitz|theorem HasCompactMulSupport.uniformContinuous_of_continuous|theorem UniformContinuous.comp_tendstoUniformlyOn |theorem tendstoUniformlyOn_iff \{F : ι → β → α\}|theorem setIntegral_eq_integral_of_forall_compl_eq_zero \(h|theorem norm_setIntegral_le_of_norm_le_const \{C|theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume|theorem norm_fderiv_le_of_lipschitz \{|theorem ae_tendsto_average_norm_sub' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'finrank_range_of_inj|bounded_above_of_compact_support|integrableOn_of_bounded|euclideanHausdorffMeasure_eq_volume|exists_antilipschitzWith' <snapshot>/mathlib/Mathlib --glob '*.lean'; rg -n 'theorem coe_range|theorem range_coe' <snapshot>/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `rg -n 'codim1_lurpt|Submission\.' <snapshot>/project --glob '*.lean' (no match); rg -n 'def HasApproximateTangentSpaceAt|def blowUpMap' <snapshot>/project <snapshot>/mathlib (no match)`
- `grep -rn 'theorem weighted_area_formula_lipschitz_injOn|theorem measurable_areaJacobianAt|theorem areaJacobianAt_nonneg|theorem areaJacobianAt_eq_normDet|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' .lake/packages/simongmt/Poincare/SimonGMT; rg -n 'def HasApproximateTangentSpaceAt|def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 scans of dag.json (902 to 976 nodes): accepted lean_statements containing ⨍, TendstoUniformly, 'r • c', fderiv+Tendsto, closedBall+Tendsto, '∃ J', '∫⁻ y in F'; children and statuses of piece_image_tangent-a1 and weighted_blowup_limit-a1; lean_name/statement scan for codim1_lurpt_* (no hit); depth-1 depends_on (no cycle)`
- `git grep -l -E 'codim1_lurpt_' <1663 unique ref tips> -- 'GMT/*.lean' (no match)`
- `git show {c70c9020,3e383ca4,ed6259bb,af5e0757,6858d683}:GMT/Ch07/Submission.lean and git diff -U0 against their audit base commits; appended '#print axioms' and ran lean -DautoImplicit=false with LEAN_PATH = .lake/build/lib/lean plus .lake/packages/*/.lake/build/lib/lean; git show 990fac9a (ptd speculative assembly draft)`
- `python3 scan of the imports in the Submission.lean of all 584 accepted candidate commits (15 add imports, 7 of them Poincare.SimonGMT.Chapter02.AreaLipschitz)`
- `lean -DautoImplicit=false /tmp/cpt-split/final/{Types,Assembly,ChildA,ChildB,EndToEnd}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a8fd95e0ea/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-96e209f8f6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-96e209f8f6/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-791b230798/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-3b627dcae9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-3b627dcae9/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-57d04995e6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-57d04995e6/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db8cbeb1bd/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db8cbeb1bd/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cpt-split/final/Types.lean`
- `/tmp/cpt-split/final/Assembly.lean`
- `/tmp/cpt-split/final/ChildA.lean`
- `/tmp/cpt-split/final/ChildB.lean`
- `/tmp/cpt-split/final/EndToEnd.lean`
- `/tmp/cpt-split/reuse/Check_pit_blowUp_image_setIntegral_eq_rescaled.lean`
- `/tmp/cpt-split/reuse/Check_pit_setIntegral_range_linear.lean`
- `/tmp/cpt-split/reuse/Check_doraggt_ae_rescaled_lebesgue_point.lean`
- `/tmp/cpt-split/reuse/Check_dorwbl_diff_quotient_tendstoUniformlyOn.lean`

Pins match. The snapshot manifest gives project b4d606db and Mathlib 25730c7c, which equal the workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest gives simongmt 2b366308, which equals .lake/packages/simongmt. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

The snapshot project contains no proof of the selected statement or of either new child. rg finds no match for codim1_lurpt or Submission.; HasApproximateTangentSpaceAt and blowUpMap are defined in simongmt Chapter03/Rectifiable.lean:102 and :96.

Every cited lemma exists in the snapshot Mathlib:
- LinearMap.exists_antilipschitzWith (Analysis/Normed/Module/FiniteDimension.lean:231) and ContinuousLinearMap.bound_of_antilipschitz (Normed/Operator/ContinuousLinearMap.lean:106);
- HasCompactSupport.uniformContinuous_of_continuous (HeineCantor.lean:91, to_additive), UniformContinuous.comp_tendstoUniformlyOn (UniformConvergence.lean:252) and Metric.tendstoUniformlyOn_iff (Pseudo/Basic.lean:142);
- setIntegral_eq_integral_of_forall_compl_eq_zero and norm_setIntegral_le_of_norm_le_const (Integral/Bochner/Set.lean:486, 613), and Measure.integrableOn_of_bounded (IntegrableOn.lean:716);
- Continuous.bounded_above_of_compact_support (Normed/Group/Bounded.lean:153) and LinearMap.finrank_range_of_inj (Dimension/Finrank.lean:127);
- LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume (NormDet.lean:433), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:187) and norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947);
- ae_tendsto_average_norm_sub (DensityTheorem.lean:150) and LinearMap.coe_range (Submodule/Range.lean:60; there is no range_coe).

SimonGMT 2b366308 supplies weighted_area_formula_lipschitz_injOn (AreaLipschitz.lean:101), measurable_areaJacobianAt, areaJacobianAt_eq_normDet, areaJacobianAt_nonneg and euclideanHausdorffMeasure_image_le_of_lipschitzOn. These are in scope only after adding import Poincare.SimonGMT.Chapter02.AreaLipschitz; 7 accepted candidates in this run already add that import.

DAG: four accepted declarations are reused with byte-identical frozen types:
- pit_blowUp_image_setIntegral_eq_rescaled (3e383ca4);
- pit_setIntegral_range_linear (ed6259bb);
- doraggt_ae_rescaled_lebesgue_point (af5e0757);
- dorwbl_diff_quotient_tendstoUniformlyOn (6858d683).
Recompiling each candidate with #print axioms gives only propext, Classical.choice and Quot.sound. The new names codim1_lurpt_piece_area_jacobian and codim1_lurpt_rescaled_integral_tendsto occur in no DAG node (976 nodes), in no node JSON, and in no GMT/*.lean at any of 1663 ref tips. ptd_piece_image_approxTangent_ae has the same type as the selected node but is only speculative-ready, so it is not reused.

Lean: Types.lean elaborates all 6 child types and the parent type. Assembly.lean proves the frozen parent from the five directly used children; #print axioms lists only those five plus the standard axioms. ChildA.lean proves area_jacobian with standard axioms only. ChildB.lean proves rescaled_limit from diff_quotient_uniform alone. EndToEnd.lean uses the real accepted proofs plus both new proofs and proves Submission.codim1_lur_piece_image_approxTangent_ae with only propext, Classical.choice and Quot.sound. An independent reviewer re-ran these files and accepted the split.
