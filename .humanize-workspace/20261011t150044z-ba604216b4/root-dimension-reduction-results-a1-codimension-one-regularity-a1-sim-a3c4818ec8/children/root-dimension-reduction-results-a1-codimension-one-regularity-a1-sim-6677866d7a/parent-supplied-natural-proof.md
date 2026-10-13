# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.simons_hardy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Appendix B, proof of B.2, inequalities (1)–(3) (chapter-B.txt lines 216–250), as in steps 3–4 of the parent proof. The hypothesis (HL) is verbatim the conclusion of Submission.codim1_hcp_lipschitz_smooth_approx for M; the parent discharges it with that theorem.

Notation. Fix the open O ⊇ M on which ν is C^∞. μ := μHE[m], with ∫_M … dμ meaning ∫ x in M, … ∂μHE[m]. P_y := orthogonal projection onto span tangentSpace M y; e_j the standard basis; δ_jg(y) := fderivWithin ℝ g M y (P_ye_j). |A|² is the function y ↦ Σ_j|Dν(y)(P_ye_j)|² and s := √(|A|²) = |A|. r(x) := |x|. Lap(x) := Σ_jδ_j(δ_j|A|²)(x). |∇A|²(x) := Σ_{i,j,k}((D_{P_xe_k}C)(P_xe_i)·P_xe_j)², with C(y) := Dν(y)∘P_y and D_aC := fderivWithin ℝ C M x a. Fix ψ, locally Lipschitz on M, vanishing on M ∖ C with C ⊆ M compact. The claim is (3): 2∫_M ψ²|A|²/r² dμ ≤ ∫_M |A|²·Σ_j(δ_jψ)² dμ.

0. (Preliminaries.)
 (a) M is Borel: M = closure(M) ∖ {0}, because 0 ∉ M and closure(M) ⊆ M ∪ {0}. μ(C) < ∞ by local finiteness. r > 0 on M, and r⁻² is bounded on C.
 (b) Extensions. By normal_complement, P_y = P̃(y) := Π − ν(y)⊗ν(y) for y ∈ M. So |A|² = Ã on M, where Ã(y) := Σ_j|Dν(y)(P̃(y)e_j)|² is C^∞ on O. Also s = s̃ on M, where s̃(y) := (Σ_j|Dν(y)(P̃(y)e_j)|²)^{1/2} is the Euclidean norm of the C¹ map y ↦ (Dν(y)(P̃(y)e_j))_j. Hence s̃ is locally Lipschitz on O, and s is locally Lipschitz on M. |A|², Ã and s are continuous on M.
 (c) Tangential derivatives of a function g that is locally Lipschitz on M. By tangent_fderiv, whenever g has derivative g' within M at x, δ_jg(x) = g'(P_xe_j), since P_xe_j ∈ span tangentSpace M x.
  (c1) δ_jg is bounded on every compact K ⊆ M. Cover K by finitely many sets M ∩ U_l on which g is K_l-Lipschitz. If g is differentiable within M at y ∈ M ∩ U_l with derivative g', take τ ∈ tangentSpace M y with witness γ. Then g'(τ) = (g∘γ)'(0) (chain rule within M, since γ maps into M), and |g(γ(s)) − g(y)| ≤ K_l|γ(s) − y| for small s. So |g'(τ)| ≤ K_l|τ| on tangentSpace M y, hence on its span (a subspace, by normal_complement), and |δ_jg(y)| ≤ K_l because |P_ye_j| ≤ 1. If g is not differentiable within M at y, then fderivWithin ℝ g M y = 0.
  (c2) If g vanishes on M ∖ K for a compact K ⊆ M, then δ_jg = 0 on M ∖ K. Indeed M ∖ K is relatively open in M, so g has derivative 0 within M at such points; apply tangent_fderiv.
  (c3) δ_jg is a.e. strongly measurable for μHE[m] restricted to M, by part (i) of (HL).

1. (Good points.) By the sibling rademacher (with IsEmbeddedSubmanifold 1 m M), ψ and s are differentiable within M at μ-a.e. point of M. Let G ⊆ M be the set of points where both are, so μ(M ∖ G) = 0. For x ∈ G let ψ' and s' be their derivatives within M at x.
 (a) ζ := s·ψ has derivative s(x)ψ' + ψ(x)s' within M at x (product rule), so δ_jζ(x) = s(x)δ_jψ(x) + ψ(x)δ_js(x).
 (b) |A|² = s·s on M, so |A|² has derivative 2s(x)s' within M at x (product rule, congruence on M). Hence δ_j|A|²(x) = 2s(x)δ_js(x).
 (c) δ_j(ψ²)(x) = 2ψ(x)δ_jψ(x).
 (d) If |A|²(x) = 0, then δ_js(x) = 0 for all j. s ≥ 0 on M and s(x) = 0. For τ ∈ tangentSpace M x with witness γ, s∘γ has a minimum at 0 and derivative s'(τ) there (chain rule within M), so s'(τ) = 0 (IsLocalMin.hasDerivAt_eq_zero). By linearity s' = 0 on the span, which contains P_xe_j.
 (e) If |A|²(x) > 0, then by (b) Σ_j(δ_js(x))² = Σ_j(δ_j|A|²(x))²/(4|A|²(x)).

2. (Pointwise Simons inequality (1) at good points.) For x ∈ G:
 ½Lap(x) + (|A|²(x))² ≥ 2|A|²(x)/r(x)² + Σ_j(δ_js(x))².
 By the sibling simons_identity, ½Lap(x) + (|A|²(x))² = |∇A|²(x) ≥ 0. If |A|²(x) = 0, the right side is 0 by 1(d). If |A|²(x) > 0, divide the sibling cone_defect by |A|²(x) to get |∇A|²(x) ≥ 2|A|²(x)/r(x)² + Σ_k(δ_k|A|²(x))²/(4|A|²(x)), and use 1(e). This is the printed (1), ½Δ_M|A|² + |A|⁴ ≥ 2r⁻²|A|² + |∇|A||².

3. (Stability with ζ = |A|ψ; the printed (2).) ζ := s·ψ is locally Lipschitz on M: s and ψ are locally Lipschitz and locally bounded on M. ζ vanishes on M ∖ C. The stability hypothesis gives ∫_M |A|²ζ² dμ ≤ ∫_M Σ_j(δ_jζ)² dμ. On M, |A|²ζ² = (|A|²)²ψ². On G, by 1(a):
 Σ_j(δ_jζ)² = |A|²Σ_j(δ_jψ)² + ψ²Σ_j(δ_js)² + 2sψΣ_jδ_jψδ_js.
 Each of the functions (|A|²)²ψ² = |A|²ζ², Σ_j(δ_jζ)², |A|²Σ_j(δ_jψ)², ψ²Σ_j(δ_js)², sψΣ_jδ_jψδ_js and ψ²|A|²/r² is μ⌞M-integrable. Each is a.e. strongly measurable by 0(b)–(c), vanishes on M ∖ C (0(c2)), and is bounded on C (0(a), 0(c1)). The two sides of the stability inequality are therefore genuine integrals of integrable functions. Σ_j(δ_jζ)² equals the sum of the three integrable pieces a.e. (on G), so its integral splits into the sum of their integrals. Hence
 ∫(|A|²)²ψ² ≤ ∫|A|²Σ(δ_jψ)² + ∫ψ²Σ(δ_js)² + ∫2sψΣδ_jψδ_js.   (2)

4. (Cross term by integration by parts.) On G, 2sψΣ_jδ_jψδ_js = ½Σ_jδ_j(ψ²)δ_j|A|², by 1(b) and 1(c). Apply the sibling stationary_ibp with φ := ψ² (locally Lipschitz on M, vanishing on M ∖ C), f := |A|², F := Ã, O' := O (Ã is C^∞, hence C², on O and equals |A|² on M by 0(b)), and MeasurableSet M (0(a)). It gives integrability of ψ²·Lap and ∫_M Σ_jδ_j(ψ²)δ_j|A|² dμ = −∫_M ψ²·Lap dμ. Hence ∫_M 2sψΣ_jδ_jψδ_js dμ = −½∫_M ψ²·Lap dμ.

5. (Combination; the printed (3).) Multiply 2 by ψ² ≥ 0 and integrate; this is legitimate a.e., and all terms are integrable by steps 3–4:
 −½∫ψ²Lap ≤ ∫ψ²(|A|²)² − 2∫ψ²|A|²/r² − ∫ψ²Σ(δ_js)².
 Insert this and step 4 into (2):
 ∫(|A|²)²ψ² ≤ ∫|A|²Σ(δ_jψ)² + ∫ψ²Σ(δ_js)² + ∫ψ²(|A|²)² − 2∫ψ²|A|²/r² − ∫ψ²Σ(δ_js)².
 Cancel the finite quantities ∫ψ²(|A|²)² and ∫ψ²Σ(δ_js)². This leaves 2∫_M ψ²|A|²/r² dμ ≤ ∫_M |A|²·Σ_j(δ_jψ)² dμ, which is the conclusion: 2·(∫ x in M, ψ x²·|A|²(x)/|x|² ∂μHE[m]) ≤ ∫ x in M, |A|²(x)·Σ_j(fderivWithin ℝ ψ M x (P_xe_j))² ∂μHE[m]. ∎

## Key steps

1. |A|² has the C^∞ ambient extension Ã and |A| = √|A|² is locally Lipschitz on M; by rademacher, ψ and |A| are differentiable within M a.e.
2. At good points: product/chain rules within M; δ_j|A|² = 2|A|δ_j|A|; at zeros of |A| the minimum principle gives δ_j|A| = 0.
3. simons_identity + cone_defect give the pointwise Simons inequality (1): ½Δ_M|A|² + |A|⁴ ≥ 2|x|⁻²|A|² + |∇|A||² a.e.
4. Stability with ζ = |A|ψ gives (2); the cross term equals ½∫∇(ψ²)·∇|A|² = −½∫ψ²Δ_M|A|² by stationary_ibp.
5. Insert (1)·ψ² and cancel the finite terms: 2∫ψ²|A|²/|x|² ≤ ∫|A|²|∇^Mψ|².

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
