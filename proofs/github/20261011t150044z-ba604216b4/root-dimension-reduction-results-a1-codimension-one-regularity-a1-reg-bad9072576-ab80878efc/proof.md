# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_support_cycle-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 0 (C0) of the supplied proof of CodimensionOneRegularity: Simon 7.5.1 (T = ∂[[E]] in U, chapter-07.txt lines 746–756) together with Simon Ch. 6, 2.11 (definition of spt T, chapter-06.txt lines 297–301) and Ch. 2, §4 (embedded submanifolds). This is part A0 of the previously reviewed analytic core of this node, stated as its own theorem; minimality of T is not needed for it. No DAG declaration is used.

Notation.
- H^{n+1} := μHE[n+1]; for ω ∈ 𝒟^n(U), dω is its exterior derivative (SimonGMT exteriorDerivative), a smooth (n+1)-form with tsupport dω ⊆ tsupport ω (SimonGMT tsupport_exteriorDerivative_subset).
- IsBoundaryOfRegion T E ξ_N means T(ω) = ∫_E ξ_N(x)(dω(x)) dH^{n+1}(x) for every ω ∈ 𝒟^n(U).
- “T vanishes on W” means T(ω) = 0 for every ω ∈ 𝒟^n(U) with tsupport ω ⊆ W. Z(T) is the union of all open W with closure W compact and contained in U on which T vanishes, and spt T := U ∖ Z(T) (GeometricCurrentOn.support).
- BoundaryVanishes T is True for n = 0; for n = j + 1 it says T.boundary = 0, where T.boundary(φ) = T(dφ) for φ ∈ 𝒟^j(U).

Proof. Fix P, n, U, N, E, ξ_N, T satisfying the hypotheses.
1. (n + 1 ≤ P.)
- InClassO gives N ∩ U ≠ ∅; pick y ∈ N ∩ U.
- IsEmbeddedSubmanifold 2 (n+1) N, applied at y, gives an open V ⊆ ℝ^{n+1}, an open W ∋ y and ψ : ℝ^{n+1} → ℝ^P with ψ(V) = W ∩ N and Dψ(z) injective for every z ∈ V.
- V ≠ ∅, since y ∈ W ∩ N = ψ(V). For any z ∈ V the linear map Dψ(z) : ℝ^{n+1} → ℝ^P is injective, so n + 1 = dim ℝ^{n+1} ≤ dim ℝ^P = P.
2. (spt T ⊆ U ∩ N.) spt T ⊆ U by definition. Let x ∈ U ∖ N; we show x ∉ spt T.
- Since (closure N ∖ N) ∩ U = ∅ and x ∈ U ∖ N, x ∉ closure N. As U is open and closure N is closed, there is r > 0 with closedBall(x, r) ⊆ U ∖ closure N.
- W₀ := B_{r/2}(x) is open, and closure W₀ ⊆ closedBall(x, r/2) is compact and contained in U. Moreover W₀ ∩ N = ∅.
- Let ω ∈ 𝒟^n(U) with tsupport ω ⊆ W₀. Then tsupport dω ⊆ W₀. Every point of E lies in N (E ⊆ N ∩ U), hence outside W₀, so dω = 0 at every point of E and T(ω) = ∫_E ξ_N(dω) dH^{n+1} = 0.
- So T vanishes on W₀; hence x ∈ W₀ ⊆ Z(T), i.e. x ∉ spt T.
Thus spt T ⊆ U ∩ N.
3. (∂T = 0.) For n = 0, BoundaryVanishes T is True. For n = j + 1 and φ ∈ 𝒟^j(U):
- T.boundary(φ) = T(dφ) = ∫_E ξ_N(d(dφ)) dH^{n+1} = ∫_E ξ_N(0) dH^{n+1} = 0, since d∘d = 0 (SimonGMT exteriorDerivative_sq) and ξ_N(x) is linear.
- Currents agreeing on all test forms are equal, so T.boundary = 0.
Steps 1–3 are the three conjuncts. ∎

## Key steps

1. A chart of N at a point of N ∩ U has injective derivative ℝ^{n+1} → ℝ^P, so n + 1 ≤ P.
2. A point of U ∖ N has a ball, compactly contained in U, missing closure N; test forms supported there have dω = 0 on E, so T vanishes there and spt T ⊆ U ∩ N.
3. T(dφ) = ∫_E ξ_N(d(dφ)) = 0 since d∘d = 0, so ∂T = 0 (vacuous for n = 0).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A4 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n 'theorem finrank_add_inf_finrank_orthogonal|theorem IsCompact.tendsto_subseq|theorem isOpen_iUnion_countable' local-references/123e8435b4a2469b/mathlib/Mathlib/{Analysis/InnerProductSpace/Projection/FiniteDimensional,Topology/Sequences,Topology/Bases}.lean`
- `grep -n 'def massOn|massOn_mono|def zeroRegion|def support|Zero (GeometricCurrentOn' simongmt/Poincare/SimonGMT/Chapter06/{Mass,CurrentLocalEquality,Currents}.lean`
- `grep -rn 'theorem <name>' simongmt/Poincare/SimonGMT for bvVariationOn_le_liminf_of_locallyL1, cone_simonsDefect_lower_bound, exists_final_exponent, injective_area_formula_of_injective_derivative, exteriorDerivative_affinePullbackForm, tsupport_exteriorDerivative_subset, exteriorDerivative_sq, simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le, WeakDerivativesZero.ae_eq_const`
- `header of simongmt Chapter03/FinitePerimeter.lean and Chapter05/Basic.lean; grep -rln 'Allard|DeGiorgi|BVCompact' simongmt/Poincare/SimonGMT`
- `python3 scan of dag.json: statuses and frozen types of the 8 siblings, the 5 reused names, the 6 new codim1_ names, the root theorems DensityAndTangentCones, DensityOneImpliesRegular, MinimizingImpliesStationary and dor_stationary_cycle_epsilon_regularity; keyword scan for overlapping nodes (regcomp_codim_one_preliminaries, regcomp_cop_region_support_subset, regcomp_cop_region_boundary_vanishes)`
- `for r in $(git for-each-ref refs/heads refs/remotes): git grep -l codim1_ $r -- 'GMT/*.lean' (2056 refs, no match)`
- `lean -DautoImplicit=false /tmp/codim1-v6/check/Types.lean; lean -DautoImplicit=false /tmp/codim1-v6/check/Assembly.lean (LEAN_PATH taken from .lake/build/lib/lean/GMT/Ch07/Submission.trace)`
- `ps -eo pid,lstart,args; max_nodes timeline over .humanize/swarm-configs; /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py _decompose, _solve_children, _existing_lean_name_problem, _install_parent_supplied_child_handoff; store.py ensure`
- `sed -n 560,1000p book/sources/chapter-07-source.txt (7.4–7.5.8); sed -n 1286,1330p book/sources/chapter-02-source.txt (5.6–5.8); sed -n 1300,1370p book/sources/chapter-05-source.txt (Theorem 7.1)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-audit-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/tmp/codim1-v6/check/Types.lean`
- `/tmp/codim1-v6/check/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/33c6cc03ee394bfbb35f84931b68580c.json`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib; the snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…), so the frozen types of this node and of the 8 siblings are unchanged since v5.
Library.
- The snapshot Mathlib has finrank_add_inf_finrank_orthogonal (FiniteDimensional.lean:89), IsCompact.tendsto_subseq (Sequences.lean:298) and isOpen_iUnion_countable (Bases.lean:932); the glue uses all three.
- SimonGMT supplies massOn and massOn_mono, support = U \ zeroRegion and the zero current (Chapter06). It also supplies BV lower semicontinuity (Chapter02/BV.lean:225), the Simons algebra (AppendixB/ConeDefect.lean:228, SimonsInequalities.lean:88), and the area-formula, exterior-derivative and affine-pullback lemmas cited by the children.
- Its headers state that De Giorgi's theorem (Chapter03/FinitePerimeter.lean) and Allard's theorem (Chapter05/Basic.lean) are not provided, and no BV compactness theorem exists. These remain book citations inside the children.
DAG.
- The 5 reused declarations are accepted with byte-identical types.
- DensityAndTangentCones, DensityOneImpliesRegular, MinimizingImpliesStationary and dor_stationary_cycle_epsilon_regularity are not accepted, so they cannot be reused.
- regcomp_codim_one_preliminaries and its children overlap region_support_cycle, but they are unaccepted and have other types.
- The 6 new codim1_ names are free in dag.json, GMT/, SimonGMT and all 2056 refs.
Lean.
- Types.lean elaborates all 11 child types (exit 0, only sorry warnings).
- Assembly.lean proves CodimensionOneRegularity from the 8 sibling and 11 child types taken as axioms (exit 0). Its axioms are propext, Classical.choice, Quot.sound, 5 new children and 7 siblings; no root proposition occurs.
Infrastructure. The current controller (pid 23222) runs with max_nodes = 1000 and dag.json has 457 nodes, so the 6 new nodes can be activated. The accepted v5 was dropped by the old controller, which had max_nodes = 200 loaded.
