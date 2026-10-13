# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1.diffquot_uniform-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof of dohr_eb_difference_quotient_limit: g_d -> D_e f uniformly on compact subsets, by uniform continuity of Df on a compact neighbourhood. It is stated here for an arbitrary open set U on which f is C^1 and an arbitrary compact K ⊆ U; the parent applies it with U = B_{rho + delta|e|}(x0) and K ⊆ B_rho(x0). The parent bounds g_d(x) - Df(x)e through the integral ∫_0^1 (Df(x + s d e) - Df(x)) e ds. Below the same bound comes from the mean value inequality, which avoids integration.

Notation: Df := fderiv ℝ f, and for d ∈ R, g_d(x) := d^{-1} • (f(x + d•e) - f(x)). 'Eventually in 𝓝[≠] 0' means: for all d in some set belonging to the punctured neighbourhood filter of 0 in R.

1. (Compact margin.) K is compact, U is open and K ⊆ U, so there is ε > 0 such that the closed thickening K_ε := cthickening ε K = {y : infDist(y, K) ≤ ε} satisfies K_ε ⊆ U (Mathlib IsCompact.exists_cthickening_subset_open). R^n is a proper metric space, so K_ε is compact (IsCompact.cthickening).

2. (Regularity of f.) U is open and f is C^1 on U.
   (a) f is differentiable at every z ∈ U: use ContDiffOn.differentiableOn with 1 ≠ 0, then DifferentiableOn.differentiableAt, since U ∈ 𝓝 z.
   (b) Df is continuous on U (ContDiffOn.continuousOn_fderiv_of_isOpen).
   Since K_ε ⊆ U is compact, Df is uniformly continuous on K_ε (Heine-Cantor, IsCompact.uniformContinuousOn_of_continuous).

3. (Choice of constants.) Let η > 0.
   (a) By step 2 (Metric.uniformContinuousOn_iff) there is θ > 0 such that ‖Df(w) - Df(x)‖ < η/(‖e‖ + 1) for all w, x ∈ K_ε with dist(w, x) < θ.
   (b) Put κ := min(ε, θ)/(‖e‖ + 1) > 0.
   (c) The set {d ∈ R : d ≠ 0 and |d| < κ} belongs to 𝓝[≠] 0. Indeed {d : |d| < κ} = ball(0, κ) ∈ 𝓝 0 and 𝓝[≠] 0 ≤ 𝓝 0, while {0}ᶜ ∈ 𝓝[≠] 0 (self_mem_nhdsWithin).

4. (Geometry.) Fix d with d ≠ 0 and |d| < κ, and fix x ∈ K. Then ‖d•e‖ = |d|‖e‖ ≤ |d|(‖e‖ + 1) < min(ε, θ). Hence:
   (a) closedBall(x, ‖d•e‖) ⊆ closedBall(x, ε) ⊆ K_ε (closedBall_subset_cthickening, as x ∈ K);
   (b) x + d•e ∈ closedBall(x, ‖d•e‖);
   (c) by convexity of the closed ball, the segment [x, x + d•e] lies in closedBall(x, ‖d•e‖) ⊆ K_ε ⊆ U;
   (d) x ∈ K ⊆ K_ε.

5. (Mean value inequality.) For every w ∈ [x, x + d•e] we have w ∈ K_ε, x ∈ K_ε and dist(w, x) ≤ ‖d•e‖ < θ, so ‖Df(w) - Df(x)‖ < η/(‖e‖ + 1). Moreover f is differentiable at w, since w ∈ U. The mean value inequality on the convex set [x, x + d•e], with the fixed linear map Df(x) (Convex.norm_image_sub_le_of_norm_fderiv_le'), yields
   ‖f(x + d•e) - f(x) - Df(x)(d•e)‖ ≤ (η/(‖e‖ + 1))·‖d•e‖ = (η/(‖e‖ + 1))·|d|·‖e‖.

6. (Estimate for the quotient.) By linearity Df(x)(d•e) = d•(Df(x)e). Since d ≠ 0,
   Df(x)e - g_d(x) = -d^{-1}•(f(x + d•e) - f(x) - Df(x)(d•e)).
   Therefore ‖Df(x)e - g_d(x)‖ ≤ |d|^{-1}·(η/(‖e‖ + 1))·|d|·‖e‖ = η·‖e‖/(‖e‖ + 1) < η.

7. (Conclusion.) Steps 3-6 show that for every η > 0, eventually in 𝓝[≠] 0, dist(Df(x)e, g_d(x)) < η for all x ∈ K. By Metric.tendstoUniformlyOn_iff this is exactly TendstoUniformlyOn (fun d x => d⁻¹ • (f (x + d • e) - f x)) (fun x => fderiv ℝ f x e) (𝓝[≠] 0) K. QED

Appendix (informative; checked Lean realization). The following proof of exactly the frozen type compiled without errors or warnings at the pinned toolchain (Lean 4.35.0-rc3, Mathlib 25730c7c). It was placed after the contract body, inside namespace GMT.Ch05 / namespace Submission, with the contract's opens: open MeasureTheory Metric Set Filter Topology; open scoped ENNReal NNReal; open RectifiableVarifold. #print axioms reports propext, Classical.choice, Quot.sound.

theorem dohr_eb_dql_diffQuot_tendstoUniformlyOn : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (U K : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 f U → IsCompact K → K ⊆ U → TendstoUniformlyOn (fun (d : ℝ) (x : Rn n) => d⁻¹ • (f (x + d • e) - f x)) (fun x => fderiv ℝ f x e) (𝓝[≠] 0) K := by
  intro n ℓ f U K e hU hf hK hKU
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening ε K) := hK.cthickening
  have hcont : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have huc : UniformContinuousOn (fderiv ℝ f) (cthickening ε K) :=
    hK'.uniformContinuousOn_of_continuous (hcont.mono hεU)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rw [Metric.uniformContinuousOn_iff] at huc
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨θ, hθ, hθK⟩ := huc (η / (‖e‖ + 1)) (div_pos hη he1)
  have hpos : 0 < min ε θ / (‖e‖ + 1) := div_pos (lt_min hε hθ) he1
  have hev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < min ε θ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with d hd
    simpa [Real.dist_eq] using hd
  filter_upwards [hev, self_mem_nhdsWithin] with d hd hd0
  have hd0' : d ≠ 0 := hd0
  intro x hx
  have hdpos : 0 < |d| := abs_pos.2 hd0'
  have hde : ‖d • e‖ < min ε θ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
      _ < min ε θ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = min ε θ := div_mul_cancel₀ _ he1.ne'
  have hball : closedBall x ‖d • e‖ ⊆ cthickening ε K :=
    (closedBall_subset_closedBall (hde.le.trans (min_le_left _ _))).trans
      (closedBall_subset_cthickening hx ε)
  have hxde : x + d • e ∈ closedBall x ‖d • e‖ := by
    rw [mem_closedBall, dist_eq_norm]; simp
  have hseg : segment ℝ x (x + d • e) ⊆ closedBall x ‖d • e‖ :=
    (convex_closedBall x _).segment_subset (mem_closedBall_self (norm_nonneg _)) hxde
  have hxK' : x ∈ cthickening ε K := self_subset_cthickening K hx
  have hmvt : ‖f (x + d • e) - f x - fderiv ℝ f x ((x + d • e) - x)‖ ≤
      η / (‖e‖ + 1) * ‖(x + d • e) - x‖ := by
    refine (convex_segment x (x + d • e)).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdiff w (hεU (hball (hseg hw)))) (fun w hw => ?_) (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _)
    have hw := hseg hw
    have hwx : dist w x < θ := by
      rw [mem_closedBall] at hw
      exact hw.trans_lt (hde.trans_le (min_le_right _ _))
    have := hθK w (hball hw) x hxK' hwx
    rw [dist_eq_norm] at this
    exact this.le
  have hsub : (x + d • e) - x = d • e := by abel
  rw [hsub] at hmvt
  rw [dist_eq_norm]
  have hrw : fderiv ℝ f x e - d⁻¹ • (f (x + d • e) - f x) =
      -(d⁻¹ • (f (x + d • e) - f x - fderiv ℝ f x (d • e))) := by
    rw [map_smul, smul_sub d⁻¹ (f (x + d • e) - f x) (d • fderiv ℝ f x e), smul_smul,
      inv_mul_cancel₀ hd0', one_smul]; abel
  rw [hrw, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |d|⁻¹ * ‖f (x + d • e) - f x - fderiv ℝ f x (d • e)‖
      ≤ |d|⁻¹ * (η / (‖e‖ + 1) * ‖d • e‖) := by gcongr
    _ = η * (‖e‖ / (‖e‖ + 1)) := by
      rw [norm_smul, Real.norm_eq_abs]; field_simp
    _ < η * 1 := by
      gcongr
      rw [div_lt_one he1]; linarith
    _ = η := mul_one η

## Key steps

1. a compact K inside the open U has a closed epsilon-thickening K_eps ⊆ U, and K_eps is compact
2. Df is continuous on U, hence uniformly continuous on K_eps
3. for 0 < |d| < min(eps, theta)/(|e|+1) and x ∈ K, the segment [x, x+de] lies in K_eps
4. the mean value inequality with fixed map Df(x) gives |f(x+de) - f(x) - Df(x)(de)| ≤ (eta/(|e|+1))|d||e|
5. dividing by d gives |g_d(x) - Df(x)e| < eta uniformly on K, i.e. TendstoUniformlyOn along 𝓝[≠] 0

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; cmp GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Contract.lean; git rev-parse HEAD`
- `grep -rn 'theorem hasFDerivAt_of_tendstoUniformlyOnFilter|theorem hasFDerivAt_of_tendstoLocallyUniformlyOn|theorem hasFDerivAt_of_tendstoUniformlyOn ' <snapshot>/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean (sed -n 290,440p)`
- `grep -rnE '(theorem|lemma|instance)[^:]*(exists_cthickening_subset_open|IsCompact.cthickening|closedBall_subset_cthickening|norm_image_sub_le_of_norm_hasFDerivWithin_le\'|norm_image_sub_le_of_norm_fderiv_le|tendstoUniformlyOn_iff|uniformContinuousOn_iff|contDiffOn_succ_iff_fderiv_of_isOpen|continuousOn_fderiv_of_isOpen|contDiffOn_zero|opNorm_le_bound|hasFDerivAt_comp_add_right|UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto|UniformCauchySeqOn.cauchy_map|cauchy_map_iff_exists_tendsto|tendsto_nhds_limUnder|Eventually.prod_mk|uniformCauchySeqOn_iff|IsCompact.uniformContinuousOn_of_continuous|le_of_tendsto)' <snapshot>/mathlib/Mathlib --include=*.lean`
- `grep -rn 'NeBot (𝓝\[≠\]' <snapshot>/mathlib/Mathlib --include=*.lean`
- `rg -l -i 'interpolation inequalit|Landau.Kolmogorov|kolmogorov inequality' <snapshot>/mathlib/Mathlib/Analysis; rg -l -i 'difference quotient' <snapshot>/mathlib/Mathlib`
- `rg -l -i 'interpolation|difference quotient|TendstoUniformlyOn' lake-packages-25730c7c/simongmt --glob '*.lean'; rg -l -i 'difference quotient|interpolation' <snapshot>/project/GMT`
- `python3 scan of dag.json lean_name values for dql/interpolation/diffQuot/c1Holder and of lean_statement values containing TendstoUniformlyOn/TendstoLocallyUniformlyOn/UniformCauchy/𝓝[≠] or fderiv with ^ α; grep -rl dohr_eb_dql nodes dag.json <snapshot>/project <snapshot>/mathlib/Mathlib`
- `python3 -I: contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') from verifier/gmt-compare.py (comparator replay scope)`
- `lake build GMT.Ch05.Submission in scratch copy /tmp/dql-decomp-WcgsEv/proj (Lean 4.35.0-rc3, shared lake-packages-25730c7c)`
- `lake env lean Checks/Assembly.lean (3 child types as axioms in namespace Submission, frozen parent proof, comparator-style exact Submission.X targets, #print axioms)`
- `lake env lean Checks/ChildA.lean; lake env lean Checks/ChildBC.lean; lake env lean Checks/Full.lean (children proved + parent; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Filter/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/DenselyOrdered.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`

PIN AND CONTRACT. The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd, which equals the workspace HEAD, and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot contract.

NO EXISTING LEMMA COVERS THE CHILDREN.
- Nothing at the pin gives an interpolation inequality: no interpolation/Landau-Kolmogorov match in Mathlib/Analysis.
- 'difference quotient' matches only Analysis/Calculus/UniformLimitsDeriv.lean. Its private difference_quotients_converge_uniformly belongs to the uniform-limit-of-derivatives theorem, not to difference quotients of a fixed C^1 map along a direction.
- No lemma states that C^{1,alpha} bounds are closed under locally uniform limits.
- The simongmt matches (Chapter01/Lusin.lean Egorov uniformization; Chapter06 current topologies) and the project GMT tree contain nothing relevant.

API THE CHILD PROOFS USE (lines at the pin):
- hasFDerivAt_of_tendstoUniformlyOnFilter [NeBot l] (UniformLimitsDeriv.lean:308; it allows eventually-differentiable families via l ×ˢ 𝓝 x)
- Convex.norm_image_sub_le_of_norm_fderiv_le' (MeanValue.lean:549)
- IsCompact.exists_cthickening_subset_open (Thickening.lean:426), IsCompact.cthickening (:283), closedBall_subset_cthickening (:537)
- IsCompact.uniformContinuousOn_of_continuous (HeineCantor.lean:49)
- contDiffOn_succ_iff_fderiv_of_isOpen (ContDiff/Defs.lean:891), ContDiffOn.continuousOn_fderiv_of_isOpen (:916), contDiffOn_zero (:618)
- hasFDerivAt_comp_add_right (FDeriv/Add.lean:847)
- UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto (UniformConvergence.lean:499), UniformCauchySeqOn.cauchy_map (:564)
- cauchy_map_iff_exists_tendsto (UniformSpace/Cauchy.lean:420), tendsto_nhds_limUnder (Topology/Basic.lean:245)
- Metric.tendstoUniformlyOn_iff (Pseudo/Basic.lean:142), Metric.uniformContinuousOn_iff (Pseudo/Defs.lean:759)
- Filter.Eventually.prod_mk (Order/Filter/Prod.lean:155), ContinuousLinearMap.opNorm_le_bound (Normed/Operator/Basic.lean:196), le_of_tendsto (Order/OrderClosed.lean:133)
- NeBot (𝓝[≠] x) instance (DenselyOrdered.lean:248)
Metric.uniformCauchySeqOn_iff exists only for atTop, so the child proof works from the definition of UniformCauchySeqOn. ContDiffOn.differentiableOn takes 1 ≠ 0.

NAMES. No dql/interpolation/diffQuot/c1Holder lean_name exists in dag.json (431 unique names). 'dohr_eb_dql' occurs nowhere in dag.json, the node directories or the snapshot, so the three proposed names are unreserved.

LEAN CHECKS (scratch build, replayed comparator scope).
- All three child types elaborate, and comparator-style targets close by exact Submission.X.
- With the children as axioms, the frozen parent type is proved; #print axioms lists propext, Classical.choice, Quot.sound, the c1Holder child and the diffQuot child.
- Each child type was also proved in Lean (C using B). The complete chain prints only propext, Classical.choice and Quot.sound, with no errors or warnings.
