# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 4.9 (chapter-06.txt lines 1355–1366) with its proof from 4.11 (lines 1378–1402), and step 3 of the parent proof. Departure: the parent first lets σ ↓ 0 for fixed h and then lets h ↓ 0; here, for each h, the sibling cmcs_level_cutoff supplies one smooth cut-off g_h (smoothed at an h-dependent scale), so a single limit h ↓ 0 suffices. Siblings used: cmcs_cutoff_defect_bound and cmcs_level_cutoff. Notation: |·| = covectorEuclideanNorm; θ̂ is the underlying form of a test form θ; dθ̂ := exteriorDerivative θ̂; S_h := {x : t − h < f(x) < t}.
1. (Reduction.) By definition, (∂A − B).massOn W is the supremum of ofReal((∂A − B)(η)) over the admissible η, i.e. η ∈ 𝒟^k(U) with tsupport η̂ ⊆ W and |η̂(x)| ≤ 1 for all x. So (sSup_le) it suffices to fix an admissible η and prove ofReal(Z) ≤ R, where Z := (∂A − B)(η) and R := L·liminf_{h→0+} ofReal(h⁻¹)·μ(W ∩ S_h). By the definitions of subtraction of currents and of the boundary, Z = A(dη) − B(η) = ∫_{{f<t}} F dμ − ∫_{{f<t}} F' dμ', where F(x) := ξ(x)(dη̂(x)) and F'(x) := ξ'(x)(η̂(x)).
2. (Integrability.) K₀ := tsupport η̂ is compact and K₀ ⊆ U, so μ(K₀) < ∞ and μ'(K₀) < ∞. The maps η̂ and dη̂ are continuous and vanish outside K₀ (tsupport_exteriorDerivative_subset). The coefficient norm is continuous (each α ↦ α(e∘I) is continuous linear and √ is continuous), so M := sup_x |dη̂(x)| < ∞; also |η̂| ≤ 1. By the hypotheses on ξ, ξ', |F| ≤ M·1_{K₀} μ-a.e. and |F'| ≤ 1_{K₀} μ'-a.e. F and F' are a.e. strongly measurable (the continuous evaluation (Λ, α) ↦ Λ(α), isBoundedBilinearMap_apply, composed with the a.e. strongly measurable ξ, resp. ξ', and a continuous form; Continuous.comp_aestronglyMeasurable₂). Hence F ∈ L¹(μ) and F' ∈ L¹(μ').
3. (Cut-offs.) For h ∈ (0, 1) let g_h be given by the sibling cmcs_level_cutoff for f, L, t, h: g_h is C^∞, |g_h| ≤ 2, ‖Dg_h(x)‖ ≤ c_h := L/(h(1 − h/2)), Dg_h(x) ≠ 0 ⇒ x ∈ S_h, g_h = 1 on {f ≤ t − h} and g_h = 0 on {f ≥ t}. (For h ∉ (0, 1) put g_h := 0; only h ∈ (0, 1) matters for limits along 𝓝[>]0.)
4. (Estimate for fixed h ∈ (0, 1).) Let Φ_h := ∫ g_h·F dμ − ∫ g_h·F' dμ'. The sibling cmcs_cutoff_defect_bound (with g := g_h and our η) gives ofReal|Φ_h| ≤ ∫⁻ ofReal(‖Dg_h(x)‖·|η̂(x)|) dμ(x). For every x the integrand is ≤ (K₀ ∩ S_h).indicator (ofReal c_h) at x: if x ∉ K₀ then η̂(x) = 0 and |η̂(x)| = 0; if Dg_h(x) = 0 the integrand is 0; otherwise x ∈ K₀ ∩ S_h and ‖Dg_h(x)‖·|η̂(x)| ≤ c_h·1. By lintegral_mono, lintegral_indicator_const_le and monotonicity of μ (K₀ ⊆ W), ofReal|Φ_h| ≤ ofReal(c_h)·μ(K₀ ∩ S_h) ≤ ofReal(c_h)·μ(W ∩ S_h).
5. (Limit h → 0+.) The filter 𝓝[>]0 on ℝ is countably generated and nontrivial. For every x, g_h(x) → 1_{{f<t}}(x) along 𝓝[>]0: if f(x) < t then g_h(x) = 1 for 0 < h ≤ min(t − f(x), 1/2); if f(x) ≥ t then g_h(x) = 0 for all h ∈ (0, 1). For h ∈ (0, 1), g_h·F is a.e. strongly measurable (g_h is continuous) and |g_h·F| ≤ 2|F|, with 2|F| integrable; likewise for F'. By dominated convergence (tendsto_integral_filter_of_dominated_convergence), ∫ g_h·F dμ → ∫ 1_{{f<t}}·F dμ = ∫_{{f<t}} F dμ and ∫ g_h·F' dμ' → ∫_{{f<t}} F' dμ' ({f < t} is open, hence measurable; integral_indicator). Hence Φ_h → Z and ofReal|Φ_h| → ofReal|Z| (continuity of ofReal ∘ |·|).
6. (Passing to the liminf.) Since 𝓝[>]0 is nontrivial, ofReal(Z) ≤ ofReal|Z| = liminf_{h→0+} ofReal|Φ_h| ≤ liminf_{h→0+} ofReal(c_h)·μ(W ∩ S_h), using step 4 for all h ∈ (0, 1), i.e. eventually (liminf_le_liminf). For h ∈ (0, 1), c_h = (1 − h/2)⁻¹·L·h⁻¹ with nonnegative factors, so ofReal(c_h) = a_h·L·ofReal(h⁻¹) with a_h := ofReal((1 − h/2)⁻¹) (ENNReal.ofReal_mul; ofReal of the real coercion of L is L). Put u_h := ofReal(h⁻¹)·μ(W ∩ S_h); the last liminf is liminf_{h→0+} a_h·(L·u_h). Let r > 1 be real. Since a_h → ofReal 1 = 1 as h → 0+, eventually a_h ≤ ofReal r, so liminf a_h·(L·u_h) ≤ liminf ofReal(r)·L·u_h = ofReal(r)·L·liminf u_h (ENNReal.liminf_const_mul_of_ne_top, ofReal(r)·L ≠ ∞). If L·liminf u_h = ∞, then R = ∞ and ofReal(Z) ≤ R is trivial; otherwise letting r ↓ 1 gives liminf a_h·(L·u_h) ≤ L·liminf u_h = R. Hence ofReal(Z) ≤ R.
7. (Conclusion.) Step 6 holds for every admissible η; taking the supremum, (∂A − B).massOn W ≤ L·liminf_{h→0+} ofReal(h⁻¹)·μ(W ∩ {t − h < f < t}). ∎

## Key steps

1. Reduce to one admissible η: Z = ∫_{f<t} ξ(dη) dμ − ∫_{f<t} ξ'(η) dμ', with integrable integrands.
2. For h ∈ (0,1), the cut-off g_h of cmcs_level_cutoff and cmcs_cutoff_defect_bound give ofReal|Φ_h| ≤ ofReal(L/(h(1 − h/2)))·μ(W ∩ {t−h<f<t}), Φ_h := ∫ g_h ξ(dη) dμ − ∫ g_h ξ'(η) dμ'.
3. g_h → 1_{f<t} pointwise with |g_h| ≤ 2, so Φ_h → Z by dominated convergence along 𝓝[>]0.
4. Pass to the liminf and remove the factor (1 − h/2)⁻¹ → 1; take the supremum over admissible η.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n -i 'slice|slicing|cmcs_|alternatizeUncurryFin|smulRight' local-references/123e8435b4a2469b/project/GMT -g '*.lean' (only the frozen Ch06 contract definitions IsRestriction/IsSlice/SlicingTheorem with main_theorem := sorry; no proofs, no cmcs_ names)`
- `rg -n 'theorem fderiv_fun_smul|theorem alternatizeUncurryFin_apply|theorem alternatizeUncurryFin_add|theorem alternatizeUncurryFin_smul|theorem dist_normed_convolution_le|theorem normed_convolution_eq_right|theorem norm_fderiv_le_of_lipschitz|theorem reflection_sub|theorem exists_contDiff_zero_iff_one_iff_of_isClosed|theorem Monotone.ae_differentiableAt|theorem MonotoneOn.intervalIntegrable_deriv|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|lemma Monotone.deriv_nonneg|theorem liminf_const_mul_of_ne_top|theorem tendsto_integral_filter_of_dominated_convergence|theorem lintegral_indicator_const_le|theorem enorm_integral_le_lintegral_enorm|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem setIntegral_eq_zero_of_forall_eq_zero' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'contDiff_convolution_left|hasContDiffBump_of_innerProductSpace|protected def map|theorem toDual_symm_apply|lemma removeNth_insertNth|lemma insertNth_self_removeNth|theorem image_eq_one_of_notMem_mulTSupport' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn 'sq_le_sq₀|pow_le_pow_iff_left₀|enorm_eq_ofReal_abs|integral_Ioc_eq_integral_Ioo|lintegral_const_mul''|hasDerivAt_iff_tendsto_slope|Filter.EventuallyEq.fderiv_eq|contDiff_normed|hasCompactSupport_normed|Integrable.restrict|isBoundedBilinearMap_apply|Continuous.comp_aestronglyMeasurable₂' lake-packages-25730c7c/mathlib/Mathlib`
- `grep -n 'tsupport_exteriorDerivative_subset|exteriorDerivative_isTestForm|def massAdmissibleOn|def covectorEuclideanNorm|def GeometricCurrentOn.massOn|def TestFormOnConverges' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,Forms}.lean`
- `python3 scan of dag.json (514 nodes): lean_name collisions for the eight new cmcs_ names (none); nodes mentioning covectorEuclideanNorm, LipschitzWith, extDeriv, alternatizeUncurryFin (no reusable slicing, wedge or smoothing lemma); regcomp_covector_sq_sum_orthonormalBasis accepted with identical lean_statement`
- `for r in $(git for-each-ref): git grep -l cmcs_ $r -- '*.lean' (no match in 2484 refs); git show 16144a47:GMT/Ch07/Submission.lean | grep regcomp_covector_sq_sum_orthonormalBasis`
- `lean GMT/Scratch/cmcs_slicing_decomposition/Assembly.lean (nine child stubs + parent proof; #print axioms: propext, sorryAx, Classical.choice, Quot.sound)`
- `lean #check with pp.coercions for the level_cutoff and lipschitz_smoothing bounds`
- `python3 -I wedge_check.py (300 random (P ≤ 5, k ≤ P) checks of E1 and |β∧γ|²+|ι_bγ|²=|b|²|γ|²)`
- `sed -n 20,70p; 160,185p; 270,300p; 1151,1180p; 1300,1420p book/chapter-06.txt`
- `grep -n 'def _existing_lean_name_problem' -A 40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (reuse of accepted identical-type declarations allowed)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_slicing_decomposition/Assembly.lean`

Snapshot facts:
- The manifest pins project b4d606db and Mathlib 25730c7c.
- The snapshot Ch07 contract is byte-identical to the workspace Submission.lean.
- The snapshot's GMT/Ch06 contract has IsRestriction, IsSlice and SlicingTheorem only as frozen definitions with main_theorem := sorry, so there is no proof to reuse. It also contains no cmcs_ name.

What else exists:
- Neither the snapshot Mathlib nor SimonGMT Chapter06 has a slicing theorem, a coefficient-norm wedge inequality, or smoothing of Lipschitz functions with locality.
- Mathlib does provide every tool the child proofs cite. Each was found in the snapshot and the pinned packages:
  - exterior derivative and Leibniz: fderiv_fun_smul, alternatizeUncurryFin_apply/_add/_smul;
  - reflections and duality: reflection_sub, OrthonormalBasis.map, toDual_symm_apply;
  - smooth Urysohn: exists_contDiff_zero_iff_one_iff_of_isClosed;
  - convolution and bumps: HasCompactSupport.contDiff_convolution_left, ContDiffBump.dist_normed_convolution_le, normed_convolution_eq_right;
  - Lipschitz derivative bound: norm_fderiv_le_of_lipschitz;
  - limits and integrals: tendsto_integral_filter_of_dominated_convergence, ENNReal.liminf_const_mul_of_ne_top;
  - monotone functions: Monotone.ae_differentiableAt, Monotone.deriv_nonneg, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc;
  - set integrals: setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_eq_zero_of_forall_eq_zero.
- SimonGMT provides tsupport_exteriorDerivative_subset and exteriorDerivative_isTestForm, and the definitions of massOn and covectorEuclideanNorm.

DAG and Lean checks:
- The only reusable DAG result is the accepted regcomp_covector_sq_sum_orthonormalBasis. Its type is identical and it is declared at commit 16144a47; it is reused for the wedge inequality.
- None of the eight new cmcs_ names collides with any of the 514 DAG nodes or any git ref.
- All nine child types elaborate.
- The frozen parent type is proved from them in Assembly.lean using only standard axioms, apart from sorryAx coming from the stubs.
