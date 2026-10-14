# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.codazzi-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof (0c): D_τν ∈ T_x by differentiating ν(γ(s)) ∈ A₀ and |ν(γ(s))|² = 1 along curves; symmetry η·D_τν = τ·D_ην in a chart, using symmetry of ∂_j∂_iψ. Parent step 1, B.4–B.5: Codazzi from the flatness of ℝ^P. The Codazzi equation is proved here in the frame-free form that the Lean statement uses: the tangential derivative of the operator field C(y) = Dν(y)∘P_y, paired with tangent vectors.

Notation. Fix an open O ⊇ M on which ν is C^∞. T_y := tangentSpace M y; P_y := orthogonal projection onto span T_y; Π := orthogonal projection onto A₀. P̃(y)w := Πw − (ν(y)·w)ν(y) for y ∈ O; C(y) := Dν(y)∘P_y and C̃(y) := Dν(y)∘P̃(y). D²ν(x)(a, b) := D(Dν)(x)(a)(b). For a ∈ T_x, D_aC := fderivWithin ℝ C M x a.

0. (Extension.) By the sibling normal_complement, for every y ∈ M: T_y = {v ∈ A₀ : ν(y)·v = 0} (a linear subspace, so span T_y = T_y) and P_y = P̃(y). Hence C = C̃ on M. Dν is C^∞ on the open set O (ContDiffOn.fderiv_of_isOpen) and P̃ is C^∞ on O, so C̃ is C^∞ on O. Fix x ∈ M.

1. (i) Dν(x)a ∈ T_x for a ∈ T_x. Let γ witness a. ν∘γ maps (−1,1) into A₀ (ν(M) ⊆ A₀) and has derivative Dν(x)a at 0 (chain rule; ν is differentiable at x ∈ O). Its difference quotients lie in the closed subspace A₀, so Dν(x)a ∈ A₀. Also |ν(γ(s))|² = 1 for all s ∈ (−1,1), so 0 = (d/ds)|ν∘γ|²(0) = 2ν(x)·Dν(x)a. By step 0, Dν(x)a ∈ T_x.

2. (ii) Dν(x)a·b = Dν(x)b·a for a, b ∈ T_x. Apply IsEmbeddedSubmanifold 2 m M at x (the hypothesis with r = 2). It gives a chart (V, W, ψ) with ψ C² on V, injective on V, ψ(V) = W ∩ M, proper, Dψ(z) injective (z ∈ V), and x = ψ(v₀) with v₀ ∈ V. By the sibling chart_tangent_space (with r = 2), T_{ψ(v)} = range Dψ(v) for every v ∈ V. Write ∂_iψ(v) := Dψ(v)e_i (i = 1, …, m). Since ψ(v) ∈ M, ν(ψ(v))·∂_iψ(v) = 0 for all v ∈ V. The function v ↦ ν(ψ(v))·∂_iψ(v) is differentiable on V (ν is differentiable on O ∋ ψ(v), ψ is C², ∂_iψ is C¹) and vanishes on the open set V. So its partial derivative in the direction e_j at v₀ vanishes:
 Dν(x)(∂_jψ(v₀))·∂_iψ(v₀) + ν(x)·D²ψ(v₀)(e_j, e_i) = 0.
ψ is C² on the open set V, so D²ψ(v₀) is symmetric (ContDiffAt.isSymmSndFDerivAt, Analysis/Calculus/FDeriv/Symmetric.lean:533). Hence Dν(x)(∂_jψ)·∂_iψ = Dν(x)(∂_iψ)·∂_jψ at v₀ for all i, j. The bilinear form β(a, b) := Dν(x)a·b − Dν(x)b·a vanishes on pairs from the family (∂_iψ(v₀))_i, which spans T_x = range Dψ(v₀). By bilinearity, β = 0 on T_x × T_x.

3. (Formula for D_aC.) C has derivative DC̃(x) within M at x, since C = C̃ on M (step 0) and C̃ is differentiable at x ∈ O. By the sibling tangent_fderiv, D_aC = DC̃(x)a for a ∈ T_x. By the product rule, for w ∈ ℝ^P:
 DC̃(x)(a)(w) = D²ν(x)(a, P̃(x)w) + Dν(x)(DP̃(x)(a)w), with DP̃(x)(a)w = −(Dν(x)a·w)ν(x) − (ν(x)·w)Dν(x)a.
For b ∈ T_x we have P̃(x)b = b and ν(x)·b = 0. Hence
 (D_aC)(b) = D²ν(x)(a, b) − (Dν(x)a·b)·Dν(x)ν(x)   (a, b ∈ T_x).

4. (iii) Codazzi: (D_aC)(b)·d = (D_bC)(a)·d for a, b, d ∈ T_x. By step 3, (D_aC)(b)·d = D²ν(x)(a, b)·d − (Dν(x)a·b)(Dν(x)ν(x)·d). ν is C^∞ near x, so D²ν(x) is symmetric (ContDiffAt.isSymmSndFDerivAt): D²ν(x)(a, b) = D²ν(x)(b, a). Also Dν(x)a·b = Dν(x)b·a by (ii). So the right-hand side is symmetric in (a, b).

5. (iv) (D_aC)(b)·d = (D_aC)(d)·b for a, b, d ∈ T_x.
 (a) For y ∈ M and u, w ∈ ℝ^P: C(y)u·w = Dν(y)(P_yu)·(P_yw). Indeed P_yu ∈ T_y, so Dν(y)(P_yu) ∈ T_y by (i) applied at y. And w − P_yw ⊥ T_y.
 (b) Fix u, w ∈ ℝ^P and set s(y) := C(y)u·w − C(y)w·u. By (a) and (ii) applied at y (to P_yu, P_yw ∈ T_y), s(y) = 0 for every y ∈ M.
 (c) s agrees on M with s̃(y) := C̃(y)u·w − C̃(y)w·u, which is differentiable at x. So s has derivative Ds̃(x) within M at x. s also has derivative 0 within M at x, since s vanishes on M. By tangent_fderiv applied to both, Ds̃(x)a = fderivWithin ℝ s M x a = 0 for a ∈ T_x. By the product rule and step 3, Ds̃(x)a = (D_aC)(u)·w − (D_aC)(w)·u. Taking u := b and w := d gives (iv).

Steps 1, 2, 4 and 5 are the four conjuncts of the conclusion. ∎

## Key steps

1. Differentiate ν(γ(s)) ∈ A₀ and |ν(γ(s))|² = 1 along curves: Dν(x)a ∈ A₀ ∩ ν(x)^⊥ = T_x.
2. In a C² chart, differentiate ν(ψ(v))·∂_iψ(v) = 0; symmetry of D²ψ gives symmetry of Dν(x) on T_x.
3. C = C̃ := Dν∘(Π − ν⊗ν) on M, so D_aC = DC̃(x)a and (D_aC)(b) = D²ν(x)(a,b) − (Dν(x)a·b)Dν(x)ν(x) for a, b ∈ T_x.
4. Symmetry of D²ν(x) and (ii) give Codazzi (iii).
5. C(y)u·w is symmetric in (u,w) for y ∈ M; differentiating this identity along M gives (iv).

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
