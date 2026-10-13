# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.normal_complement-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof (0b): "T_x is an m-dimensional linear subspace (chart_tangent_space), T_x ⊆ A₀ (velocities of curves in M ⊆ A₀), A₀ = T_x ⊕ ℝν(x) orthogonally". The projection formula is the explicit form of that orthogonal decomposition.

Fix x ∈ M. Write T := tangentSpace M x, H := {v ∈ ℝ^P : v ∈ A₀ and ν(x)·v = 0}, and Π := A₀.starProjection, the orthogonal projection onto A₀.

1. (T is an m-dimensional linear subspace.) IsEmbeddedSubmanifold 1 m M at the point x gives open V ⊆ ℝ^m and W ⊆ ℝ^P with x ∈ W, and a map ψ : ℝ^m → ℝ^P with the following properties: ψ is C¹ on V and injective on V; ψ(V) = W ∩ M; V ∩ ψ⁻¹(K) is compact for every compact K ⊆ W; and Dψ(z) is injective for z ∈ V. Since x ∈ W ∩ M = ψ(V), we have x = ψ(v₀) with v₀ ∈ V. The accepted sibling chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv, with r = 1 and N = M) gives T = range Dψ(v₀). So T is the range of an injective linear map ℝ^m → ℝ^P, hence a linear subspace of dimension m.

2. (T ⊆ A₀.) Let v ∈ T with witness γ (C¹ on (−1,1), γ((−1,1)) ⊆ M, γ(0) = x, γ'(0) = v). For 0 < |s| < 1, γ(s) and γ(0) lie in M ⊆ A₀, so the difference quotient (γ(s) − γ(0))/s lies in A₀. These quotients converge to v as s → 0. A₀ is finite-dimensional, hence closed, so v ∈ A₀.

3. (T ⊆ H.) Combine step 2 with the hypothesis ν(x)·v = 0 for v ∈ T.

4. (dim H = m.) H is the kernel of the linear functional λ : A₀ → ℝ, λ(w) := ν(x)·w. Since ν(x) ∈ A₀ and λ(ν(x)) = |ν(x)|² = 1, λ is surjective. By rank–nullity, dim H = dim A₀ − 1 = (m + 1) − 1 = m.

5. (T = H.) T ⊆ H are subspaces of the same finite dimension m (steps 1, 3, 4), so T = H (Submodule.eq_of_le_of_finrank_eq). This is the first claim, an equality of sets.

6. (Projection formula.) By step 5, span T = T = H. Fix w ∈ ℝ^P and put u := Πw − (ν(x)·w)ν(x).
 (a) u ∈ H. Πw and ν(x) lie in A₀, so u ∈ A₀. Also ν(x)·u = ν(x)·Πw − (ν(x)·w)|ν(x)|² = (Πν(x))·w − ν(x)·w = 0, because Π is self-adjoint and Πν(x) = ν(x) (ν(x) ∈ A₀).
 (b) w − u ⊥ H. Let h ∈ H ⊆ A₀. Then (w − Πw)·h = 0 since w − Πw ⊥ A₀, and ν(x)·h = 0. So (w − u)·h = (w − Πw)·h + (ν(x)·w)(ν(x)·h) = 0.
 The orthogonal projection onto the closed subspace H is the unique point u ∈ H with w − u ⊥ H (Mathlib Submodule.eq_starProjection_of_mem_of_inner_eq_zero). Therefore (Submodule.span ℝ T).starProjection w = u = Πw − (ν(x)·w)ν(x). ∎

## Key steps

1. A chart at x and chart_tangent_space give tangentSpace M x = range Dψ(v₀), an m-dimensional subspace.
2. Velocities of curves in M ⊆ A₀ lie in the closed subspace A₀, and they are ⊥ ν(x) by hypothesis.
3. A₀ ∩ ν(x)^⊥ has dimension m (rank–nullity, ν(x) ∈ A₀ a unit vector), so the inclusion is an equality.
4. u := Πw − (ν(x)·w)ν(x) lies in A₀ ∩ ν(x)^⊥ and w − u is orthogonal to it, so u is the orthogonal projection.

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
