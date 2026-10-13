# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.wedge_norm-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (E1) of the parent proof (|β ∧ γ| ≤ |β||γ|, proved there by rotating β to a multiple of a basis vector), with Simon's wedge product (Ch. 6, 1.1–1.3, chapter-06.txt lines 26–60) and Euclidean norm (1.15, line 178). We use the sibling regcomp_covector_sq_sum_orthonormalBasis, denoted (Σ): for every m ∈ ℕ, every m-covector α and every orthonormal basis f = (f_0, …, f_{P−1}) of ℝ^P indexed by Fin P, Σ_{j : Fin m → Fin P} α(f∘j)² = m!·|α|², where f∘j := (f_{j(0)}, …, f_{j(m−1)}).
Put ω := alternatizeUncurryFin (β.smulRight γ). By alternatizeUncurryFin_apply and (β.smulRight γ)(v) = β(v)·γ, for every v : Fin (k+1) → ℝ^P we have ω(v) = Σ_{i : Fin (k+1)} (−1)^i·β(v_i)·γ(Fin.removeNth i v).
1. (Riesz representative.) Let b := (InnerProductSpace.toDual ℝ (Euclid P)).symm β. Then β(v) = ⟨b, v⟩ for every v (toDual_symm_apply) and ‖b‖ = ‖β‖ (toDual is a linear isometry equivalence).
2. (Case b = 0.) Then β = 0, so β.smulRight γ = 0 and ω = 0 (alternatizeUncurryFin is the continuous linear map alternatizeUncurryFinCLM, which maps 0 to 0). Hence |ω| = 0 ≤ ‖β‖·|γ| (covectorEuclideanNorm_zero, |γ| ≥ 0). From now on b ≠ 0; then ℝ^P ≠ {0}, so P ≥ 1 and 0 ∈ Fin P.
3. (An orthonormal basis adapted to b.) Let u := ‖b‖⁻¹·b, so ‖u‖ = 1, and let e := EuclideanSpace.basisFun (Fin P) ℝ. Let R := reflection (ℝ ∙ (e_0 − u))ᗮ, a linear isometry equivalence of ℝ^P; since ‖e_0‖ = 1 = ‖u‖, R(e_0) = u (reflection_sub). The family f := e.map R (OrthonormalBasis.map), f_i = R(e_i), is an orthonormal basis of ℝ^P indexed by Fin P with f_0 = u. By orthonormality β(f_i) = ⟨b, f_i⟩ = ‖b‖·⟨f_0, f_i⟩, which equals ‖b‖ for i = 0 and 0 for i ≠ 0.
4. (Values on basis tuples.) Let j : Fin (k+1) → Fin P; note Fin.removeNth i (f∘j) = f∘(Fin.removeNth i j). By step 3, ω(f∘j) = ‖b‖·Σ_{i : j(i) = 0} (−1)^i·γ(f∘(Fin.removeNth i j)).
(a) If j is not injective, then f∘j is not injective (f is injective), so ω(f∘j) = 0 because ω is alternating (ContinuousAlternatingMap.map_eq_zero_of_not_injective).
(b) If j is injective, at most one index i has j(i) = 0, so the sum has at most one term and ω(f∘j)² = ‖b‖²·Σ_{i : j(i) = 0} γ(f∘(Fin.removeNth i j))².
Hence in all cases (∗) ω(f∘j)² ≤ ‖b‖²·Σ_{i : Fin (k+1)} [j(i) = 0]·γ(f∘(Fin.removeNth i j))², since in case (a) the left side is 0 and the right side is a sum of squares.
5. (Summation.) Summing (∗) over all j : Fin (k+1) → Fin P and exchanging the finite sums, Σ_j ω(f∘j)² ≤ ‖b‖²·Σ_{i : Fin (k+1)} Σ_{j : j(i) = 0} γ(f∘(Fin.removeNth i j))². For fixed i, j ↦ Fin.removeNth i j is a bijection from {j : Fin (k+1) → Fin P | j(i) = 0} onto Fin k → Fin P with inverse j' ↦ Fin.insertNth i 0 j' (Fin.removeNth_insertNth, and Fin.insertNth_self_removeNth together with j(i) = 0). So the inner sum equals Σ_{j' : Fin k → Fin P} γ(f∘j')² = k!·|γ|² by (Σ) with m = k. Therefore Σ_j ω(f∘j)² ≤ ‖b‖²·(k+1)·k!·|γ|² = (k+1)!·‖b‖²·|γ|².
6. (Conclusion.) By (Σ) with m = k+1 and α = ω, Σ_j ω(f∘j)² = (k+1)!·|ω|². Hence (k+1)!·|ω|² ≤ (k+1)!·(‖b‖·|γ|)², and since (k+1)! > 0, |ω|² ≤ (‖b‖·|γ|)². Both |ω| and ‖b‖·|γ| are nonnegative (covectorEuclideanNorm is a square root), so |ω| ≤ ‖b‖·|γ| = ‖β‖·|γ| (sq_le_sq₀: for nonnegative reals a² ≤ c² ↔ a ≤ c). ∎

## Key steps

1. Write β = ⟨b, ·⟩ with ‖b‖ = ‖β‖; the case b = 0 is trivial.
2. Choose an orthonormal basis f with f_0 = b/‖b‖ (reflection of the standard basis), so β(f_i) = ‖b‖δ_{i0}.
3. On basis tuples, (β∧γ)(f∘j)² ≤ ‖b‖² Σ_i [j(i) = 0] γ(f∘removeNth i j)² (non-injective tuples give 0).
4. Summing and using removeNth/insertNth bijections and the basis-invariant square sum (Σ) twice gives (k+1)!|β∧γ|² ≤ (k+1)!‖b‖²|γ|².

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
