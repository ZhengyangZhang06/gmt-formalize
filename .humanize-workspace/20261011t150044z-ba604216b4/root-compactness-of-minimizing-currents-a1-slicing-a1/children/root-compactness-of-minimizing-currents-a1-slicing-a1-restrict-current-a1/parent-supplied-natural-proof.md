# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.restrict_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 2.9 (chapter-06.txt lines 283–288: T⌞A(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T) and step 1 of the parent proof, here for an arbitrary representation (μ, ξ) and an arbitrary set E. For a test form ω write ω̂ := (ω : DifferentialForm (Euclid P) n) for its underlying form, and put ν := μ.restrict E, so that ∫_E G dμ = ∫ G dν. Since ν ≤ μ (Measure.restrict_le_self), ν(K) ≤ μ(K) < ∞ for every compact K ⊆ U, and every μ-a.e. property holds ν-a.e. (ae_restrict_of_ae).
1. (Norm comparison.) Let N be the number of strictly increasing I : Fin n → Fin P and C := √N. For every n-covector α and every such I, |α(e_{I(0)}, …, e_{I(n−1)})| ≤ ‖α‖·∏_i ‖e_{I(i)}‖ = ‖α‖ (le_opNorm for the continuous alternating map α; the standard basis vectors have norm 1). Hence |α|² = Σ_{I strictly increasing} α(e∘I)² ≤ N·‖α‖², i.e. |α| ≤ C‖α‖.
2. (Integrability.) Fix ω ∈ 𝒟ⁿ(U). K := tsupport ω̂ is compact (ω̂ has compact support) and K ⊆ U, so μ(K) < ∞; ω̂ is continuous with compact support, so M_ω := sup_x ‖ω̂(x)‖ < ∞. The integrand F_ω(x) := ξ(x)(ω̂(x)) is μ-a.e. strongly measurable: it is the continuous evaluation map (Λ, α) ↦ Λ(α) on MultiVector P n × Λⁿ (isBoundedBilinearMap_apply) composed with the a.e. strongly measurable ξ and the continuous ω̂ (Continuous.comp_aestronglyMeasurable₂). For μ-a.e. x, |F_ω(x)| ≤ |ω̂(x)| ≤ C‖ω̂(x)‖ ≤ C·M_ω·1_K(x), because ω̂(x) = 0 for x ∉ K (image_eq_zero_of_notMem_tsupport) and ξ(x)(0) = 0. The bound C·M_ω·1_K is μ-integrable since μ(K) < ∞, so F_ω is μ-integrable and hence ν-integrable (Integrable.restrict); the same bound holds ν-a.e.
3. (Linearity.) Define S₀(ω) := ∫ F_ω dν. For ω₁, ω₂ ∈ 𝒟ⁿ(U) and c ∈ ℝ, F_{ω₁+ω₂} = F_{ω₁} + F_{ω₂} and F_{cω} = c·F_ω pointwise, since the coercion of test forms is linear and every ξ(x) is linear. By step 2 and integral_add, S₀(ω₁ + ω₂) = S₀(ω₁) + S₀(ω₂); by integral_const_mul (which needs no integrability), S₀(cω) = c·S₀(ω). So S₀ is a linear map 𝒟ⁿ(U) → ℝ.
4. (Sequential continuity.) Let (ω_j) satisfy TestFormOnConverges ω_j 0: there is a compact K ⊆ U with tsupport ω̂_j ⊆ K for all j and, for derivative order 0, iteratedFDeriv ℝ 0 ω̂_j → iteratedFDeriv ℝ 0 0 = 0 uniformly on K. As ‖iteratedFDeriv ℝ 0 G x‖ = ‖G(x)‖ (norm_iteratedFDeriv_zero), for every ε > 0 there is j₀ with ‖ω̂_j(x)‖ ≤ ε for all j ≥ j₀ and x ∈ K, while ω̂_j(x) = 0 for x ∉ K. As in step 2, for j ≥ j₀, |F_{ω_j}| ≤ C·ε·1_K ν-a.e., so |S₀(ω_j)| ≤ ∫ |F_{ω_j}| dν ≤ C·ε·ν(K) ≤ C·ε·μ(K) (norm_integral_le_integral_norm, integral_mono_ae). Since μ(K) < ∞ and ε > 0 is arbitrary, S₀(ω_j) → 0.
5. (Conclusion.) By steps 3–4, S := ⟨S₀, continuity⟩ is a GeometricCurrentOn U n, and S(ω) = ∫_E ξ(x)(ω̂(x)) dμ(x) for every ω ∈ 𝒟ⁿ(U). ∎

## Key steps

1. The Euclidean coefficient norm is dominated by a constant times the operator norm.
2. For a test form ω the integrand ξ(ω) is a.e. strongly measurable and bounded by C·sup‖ω‖·1_{tsupport ω}, which is integrable because μ(tsupport ω) < ∞; restriction to E preserves this.
3. ω ↦ ∫_E ξ(ω) dμ is linear (integral_add, integral_const_mul).
4. If ω_j → 0 in 𝒟ⁿ(U) with supports in a compact K ⊆ U, then |S(ω_j)| ≤ C·sup_K‖ω_j‖·μ(K) → 0, so S is a GeometricCurrentOn U n.

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
