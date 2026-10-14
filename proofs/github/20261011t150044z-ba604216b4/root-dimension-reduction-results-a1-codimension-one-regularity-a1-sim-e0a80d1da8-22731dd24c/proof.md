# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.stationary_ibp-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof (4c), integration by parts via stationarity and the Lipschitz approximation sibling (the grandparent's lipschitz_approx). The parent builds the vector field from graph charts and a partition of unity. Here the tangential gradient has the explicit ambient C¹ extension V := P̃∇F with P̃ := Π − ν⊗ν (normal_complement), so a single cut-off β replaces the partition of unity. The hypothesis (HL) is verbatim the conclusion of Submission.codim1_hcp_lipschitz_smooth_approx for M.

Notation. Fix the open O ⊇ M on which ν is C^∞, and f, F, O' as in the statement (F is C² on the open O' ⊇ M and F = f on M). Let μ := μHE[m] restricted to M (∫_M … dμ means ∫ x in M, … ∂μHE[m]). T_y := tangentSpace M y; P_y := orthogonal projection onto span T_y; e_j the standard basis. δ_jg(y) := fderivWithin ℝ g M y (P_ye_j). lap f(x) := Σ_jδ_j(δ_jf)(x). U := (O ∩ O') ∖ {0}, an open set containing M (0 ∉ M). Fix φ, locally Lipschitz on M, vanishing on M ∖ C with C ⊆ M compact.

1. (Smooth extensions.) By normal_complement, P_y = P̃(y) for y ∈ M, where P̃(y)w := Πw − (ν(y)·w)ν(y) is C^∞ on O. Put G_j(y) := DF(y)(P̃(y)e_j), C¹ on O ∩ O', and V(y) := Σ_j G_j(y)e_j. Then V is C¹ on O ∩ O', and for y ∈ M, V(y) = P_y∇F(y) ∈ T_y. Indeed G_j(y) = ∇F(y)·P_ye_j = P_y∇F(y)·e_j. By tangent_fderiv (F = f on M, F differentiable at y): δ_jf(y) = DF(y)(P_ye_j) = G_j(y) for y ∈ M. Applying it again to δ_jf = G_j on M: δ_j(δ_jf)(x) = DG_j(x)(P_xe_j). So δ_jf and lap f are continuous on M, being restrictions of continuous functions on O ∩ O'.

2. (Tangential derivatives of Lipschitz functions.) Let g be locally Lipschitz on M.
 (a) |δ_jg| is bounded on every compact K ⊆ M. Cover K by finitely many sets M ∩ U_l on which g is K_l-Lipschitz. If g is differentiable within M at y, then for τ ∈ T_y with witness γ, fderivWithin ℝ g M y τ = (g∘γ)'(0) (chain rule within M; γ maps into M), and |g(γ(s)) − g(y)| ≤ K_l|γ(s) − y|. Hence |fderivWithin ℝ g M y τ| ≤ K_l|τ|, so |δ_jg(y)| ≤ K_l since P_ye_j ∈ span T_y = T_y and |P_ye_j| ≤ 1. If g is not differentiable within M at y, then fderivWithin ℝ g M y = 0.
 (b) If g vanishes on M ∖ K for a compact K ⊆ M, then δ_jg = 0 on M ∖ K. M ∖ K is relatively open in M, so g vanishes on M near y. Hence g has derivative 0 within M at y, and tangent_fderiv applies.
 (c) δ_jg is μ-a.e. strongly measurable, by part (i) of (HL).

3. (Integrability.) M is a Borel set (hypothesis). Let K₀ := C; μ(K₀) < ∞ by local finiteness. The function x ↦ Σ_jδ_jφ(x)δ_jf(x) is a.e. strongly measurable (2(c), and δ_jf is continuous on M). It vanishes on M ∖ C (2(b)) and is bounded on C (2(a) and continuity of δ_jf on the compact C), so it is μ-integrable. Similarly φ·lap f is a.e. strongly measurable: φ is continuous on M, and lap f is continuous on M (step 1). It vanishes on M ∖ C and is bounded on C, so it is integrable. These are the first two conjuncts.

4. (Approximation.) By part (ii) of (HL) applied to φ, there are a compact C'' ⊆ M and C^∞ functions χ_k with compact support such that: χ_k = 0 on M ∖ C''; χ_k → φ uniformly on M; and ∫⁻_M Σ_j(Dχ_k(x)(P_xe_j) − δ_jφ(x))² dμ → 0. By tangent_fderiv, Dχ_k(x)(P_xe_j) = δ_jχ_k(x) for x ∈ M. Let K := C ∪ C'', a compact subset of M.

5. (Cut-off.) K is a compact subset of the open set U. Choose an open W₁ with K ⊆ W₁ and closure(W₁) ⊆ U compact, and a C^∞ function β : ℝ^P → [0, 1] with β = 1 on a neighbourhood of K and tsupport β ⊆ W₁. (Use Mathlib exists_contDiff_support_eq_eq_one_iff, Geometry/Manifold/PartitionOfUnity.lean:789, with s := W₁ and t := closure of an open W₂, K ⊆ W₂ ⊆ closure(W₂) ⊆ W₁.) Define X_k(z) := χ_k(z)β(z)V(z) for z ∈ U and X_k(z) := 0 otherwise. X_k is C¹ on U and vanishes on the open set ℝ^P ∖ tsupport β. These two open sets cover ℝ^P, so X_k is C¹ on ℝ^P. Its support lies in the compact set tsupport β ⊆ U, so X_k has compact support and 0 ∉ tsupport X_k.

6. (Tangential divergence of X_k.) For a C¹ field X and x ∈ M:
 trace(P_x∘DX(x)) = trace(DX(x)∘P_x) = Σ_j e_j·DX(x)(P_xe_j) = Σ_j δ_j(X·e_j)(x),
using cyclicity of the trace, the matrix of DX(x)∘P_x, and tangent_fderiv. Claim: for x ∈ M,
 trace(P_x∘DX_k(x)) = Σ_jδ_jχ_k(x)δ_jf(x) + χ_k(x)·lap f(x).
 (a) If x ∈ K, then β = 1 near x, so X_k = χ_kV near x and X_k·e_j = χ_kG_j there. By the product rule, D(χ_kG_j)(x)(P_xe_j) = Dχ_k(x)(P_xe_j)G_j(x) + χ_k(x)DG_j(x)(P_xe_j) = δ_jχ_k(x)δ_jf(x) + χ_k(x)δ_j(δ_jf)(x), by steps 1 and 4. Sum over j.
 (b) If x ∈ M ∖ K, then χ_k = 0 on the relatively open set M ∖ C'' ∋ x. So X_k·e_j and χ_k vanish on M near x, and their tangential derivatives at x vanish (2(b)). Both sides of the claim are 0 (χ_k(x) = 0).

7. (Stationarity.) X_k is C¹ with compact support and 0 ∉ tsupport X_k (step 5). The stationarity hypothesis and step 6 give ∫_M (Σ_jδ_jχ_kδ_jf + χ_k·lap f) dμ = 0 for every k. Both summands are integrable: they are continuous on M, zero on M ∖ K, and bounded on K.

8. (Limit.) Let B := sup_K (Σ_j(δ_jf)²)^{1/2} and L := sup_K|lap f|, both finite by continuity on the compact K. All functions below vanish on M ∖ K. By Cauchy–Schwarz in j and then in L²(μ⌞K):
 ∫_M|Σ_j(δ_jχ_k − δ_jφ)δ_jf| dμ ≤ B·μ(K)^{1/2}·(∫_M Σ_j(δ_jχ_k − δ_jφ)² dμ)^{1/2} → 0, by step 4;
 ∫_M|χ_k − φ|·|lap f| dμ ≤ L·μ(K)·sup_M|χ_k − φ| → 0.
 Hence ∫_M(Σ_jδ_jφδ_jf + φ·lap f) dμ = lim_k ∫_M(Σ_jδ_jχ_kδ_jf + χ_k·lap f) dμ = 0. By step 3 both summands are integrable, so the integral splits:
 ∫_M Σ_jδ_jφδ_jf dμ = −∫_M φ·lap f dμ.
This is the third conjunct, and with step 3 the proof is complete. ∎

## Key steps

1. δ_jf = G_j := DF(P̃e_j) on M with P̃ = Π − ν⊗ν; V := Σ_jG_je_j = P∇F is an ambient C¹ tangent extension of ∇^Mf; Δ_Mf continuous on M.
2. Tangential derivatives of locally Lipschitz functions are bounded on compacts, vanish off the support, and are measurable by (HL)(i): integrability.
3. (HL)(ii) approximants χ_k and a cut-off β give X_k := χ_kβV, C¹ with compact support avoiding 0; div_M X_k = Σ_jδ_jχ_kδ_jf + χ_kΔ_Mf on M.
4. Stationarity: ∫_M(Σ_jδ_jχ_kδ_jf + χ_kΔ_Mf) = 0; pass to the limit with Cauchy–Schwarz and the L² gradient convergence of (HL)(ii).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `rg -n 'Simons|Codazzi|Laplace|second fundamental' project/GMT`
- `rg -n 'def tangentSpace|def IsEmbeddedSubmanifold' project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem HasFDerivWithinAt.unique_on|theorem DifferentiableWithinAt.hasFDerivWithinAt|mem_tangentConeAt_of_seq|irreducible_def tangentConeAt|irreducible_def fderivWithin' mathlib/Mathlib/Analysis/Calculus`
- `rg -n 'hausdorffMeasure_smul₀|hausdorffMeasure_image_le|EuclideanSpace.euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib`
- `rg -n '^theorem|^lemma' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n 'isSymmSndFDerivAt|exists_orthonormalBasis_extension|ContDiffOn.fderiv_of_isOpen|exists_contDiff_support_eq_eq_one_iff|eq_starProjection_of_mem_of_inner_eq_zero|eq_of_le_of_finrank_eq|IsLocalMin.hasDerivAt_eq_zero|tendsto_integral_of_dominated_convergence|ContinuousOn.aestronglyMeasurable|ae_restrict_iff' mathlib/Mathlib`
- `rg -n 'def localInverse|theorem eventually_left_inverse|theorem to_localInverse' mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem`
- `rg -n 'theorem exists_smooth_tsupport_subset|theorem HasStrictFDerivAt.to_localInverse|theorem LocallyLipschitzOn' mathlib/Mathlib (no match under these exact names)`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/AppendixB/{SimonsInequalities,ConeDefect,LagrangeIdentity}.lean; lean Avail.lean: #check Poincare.SimonGMT.AppendixB.cone_simonsDefect_lower_bound after import GMT.Ch07.Submission`
- `python3 scans of dag.json (nodes under hypercone_plane-a1, statuses and frozen types of chart_tangentSpace_eq_range_fderiv, dimred_rpd_submanifold_density_one, codim1_hcp_lipschitz_smooth_approx, codim1_hcp_smooth_charts); grep -c codim1_hcp_sc dag.json; git log --all -S codim1_hcp_sc -- GMT`
- `lean -DautoImplicit=false /tmp/simons-cone-split/check/{Parent,TypesAll,Assembly,Inst}.lean with LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean`
- `python3 verifier/lean_contract.py validate_lean_statement on all 12 child types`
- `/tmp/simons-cone-venv/env/bin/python -I /tmp/simons-cone-split/scripts/jets.py {clifford,more} and generic2.py {ell,gen3,cubic}`
- `book/chapter-B.txt lines 1–282 (B.1–B.11 and proof of B.2)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/TangentCone/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/LagrangeIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-a3c4818ec8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-B.txt`
- `/tmp/simons-cone-split/check/TypesAll.lean`
- `/tmp/simons-cone-split/check/Assembly.lean`
- `/tmp/simons-cone-split/check/Inst.lean`
- `/tmp/simons-cone-split/scripts/jets.py`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c; these equal the workspace HEAD and .lake/packages/mathlib (simongmt is at 2b366308). The snapshot's project/GMT/Ch07/Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f9503aa28…).

Project: there is no Simons, Codazzi or Laplace–Beltrami development. rg finds only the Ch02 B_y doc-comment, the Ch07 'Simons cone' remark and README pointers to the AppendixB numerics. tangentSpace (Contract.lean:228) and IsEmbeddedSubmanifold (:221) are the definitions used.

Mathlib snapshot: it contains every library fact the child proofs cite.
- HasFDerivWithinAt.unique_on (FDeriv/Basic.lean:159) and DifferentiableWithinAt.hasFDerivWithinAt (:391); the fderivWithin definition (FDeriv/Defs.lean:151); mem_tangentConeAt_of_seq (TangentCone/Defs.lean:96).
- Measure.hausdorffMeasure_smul₀ (Hausdorff.lean:753); LipschitzOnWith.hausdorffMeasure_image_le (:733); LipschitzOnWith.ae_differentiableWithinAt_of_mem (Rademacher.lean:361); EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187).
- ContDiffAt.isSymmSndFDerivAt (FDeriv/Symmetric.lean:533); Orthonormal.exists_orthonormalBasis_extension (PiL2.lean:1031); ContDiffOn.fderiv_of_isOpen (ContDiff/Defs.lean:907); exists_contDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:789); HasStrictFDerivAt.localInverse, eventually_left_inverse and to_localInverse (InverseFunctionTheorem/FDeriv.lean:149–186).
- Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Projection/Basic.lean:180); Submodule.eq_of_le_of_finrank_eq (FiniteDimensional/Basic.lean:257); IsLocalMin.hasDerivAt_eq_zero (LocalExtr/Basic.lean:237); tendsto_integral_of_dominated_convergence (DominatedConvergence.lean:57); ae_restrict_iff' (Restrict.lean:629).
- No match for theorems named exists_smooth_tsupport_subset or HasStrictFDerivAt.to_localInverse. The proofs use exists_contDiff_support_eq_eq_one_iff and the namespaced inverse-function lemmas instead.

SimonGMT: AppendixB supplies the B.10–B.11 algebra (ConeDefect.lean:136–228, LagrangeIdentity.lean:122) and ε = 1/10 (SimonsInequalities.lean:88). However, #check of cone_simonsDefect_lower_bound after import GMT.Ch07.Submission gives Unknown identifier. Child statements therefore avoid it, and cone_defect's proof notes the extra import and includes the printed algebra.

DAG: chart_tangentSpace_eq_range_fderiv is accepted (candidate d626082a69a0) and is reused with an identical type. lipschitz_approx and smooth_charts are unaccepted children of this node's parent, so they cannot be reused here. lipschitz_approx's exact conclusion is passed as hypothesis (HL), and density one as a hypothesis; the parent discharges both from its own resolved dependencies. The codim1_hcp_sc_ names are free in dag.json, in the git history and in all reference trees.

Lean: all 12 types elaborate (TypesAll, exit 0), and the parent's frozen type is kernel-checked from them (Assembly, exit 0).
