# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_campanato-a1.c1_holder_extension-a1`
- Child DAG node: `root.allard_regularity-a1.graph_campanato-a1.c1_holder_extension-a1.holder_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 4 of the parent proof, with an arbitrary map F in place of Df and an arbitrary set S contained in the closure of Z in place of the ball B. The comparison of step 1 is supplied by the sibling child hs_norm_basics. The density of Z in B is step 2 of the parent proof and is proved in the parent.

Notation.
- L := L(R^m, R^k) is the space of continuous linear maps R^m -> R^k with the operator norm ||.||. L is complete, because its codomain R^k is complete. As a normed space it is Hausdorff and regular.
- kappa(t) := M (t/R)^alpha for real t (real power). The hypothesis then reads hsNorm(F x - F y) <= kappa(||x - y||) for x, y in Z.
- For x in R^n, nhdsWithin x Z denotes the filter of neighbourhoods of x within Z.
- The sibling child hs_norm_basics (allard52_c1h_opNorm_le_hsNorm_continuous with these m, k) gives:
  (HS1) ||T|| <= hsNorm(T) for every T in L;
  (HS2) T -> hsNorm(T) is continuous on L.

1. Properties of kappa.
- Since alpha >= 0, t -> t^alpha is continuous on R (Real.continuous_rpow_const). So kappa is continuous: compose with t -> t/R, then multiply by the constant M.
- Since alpha != 0, 0^alpha = 0 (Real.zero_rpow), so kappa(0) = 0.
- kappa is nondecreasing on [0, infinity). If 0 <= s <= t, then 0 <= s/R <= t/R because R > 0, so (s/R)^alpha <= (t/R)^alpha (Real.rpow_le_rpow, exponent alpha >= 0). Multiplying by M >= 0 gives kappa(s) <= kappa(t).

2. Small modulus. For every epsilon > 0 there is eta > 0 with kappa(2 eta) < epsilon. The function eta -> kappa(2 eta) is continuous (step 1) and takes the value kappa(0) = 0 at eta = 0. So there is delta > 0 with |kappa(2 eta)| < epsilon whenever |eta| < delta, and eta := delta/2 > 0 works.

3. Limits along Z exist. Let x be in closure Z.
- nhdsWithin x Z is a nontrivial filter (mem_closure_iff_nhdsWithin_neBot), hence so is its image under F.
- The image filter is Cauchy (Metric.cauchy_iff). Given epsilon > 0, take eta from step 2 and t := F(Z cap B^o_eta(x)). Then t belongs to the image filter, because Z cap B^o_eta(x) belongs to nhdsWithin x Z.
- For z, z' in Z cap B^o_eta(x) we have ||z - z'|| <= ||z - x|| + ||z' - x|| < 2 eta. Hence dist(F z, F z') = ||F z - F z'|| <= hsNorm(F z - F z') <= kappa(||z - z'||) <= kappa(2 eta) < epsilon. This uses (HS1), the hypothesis (z, z' are in Z), and the monotonicity of kappa on [0, infinity) from step 1.
- Since L is complete, the Cauchy image filter converges (cauchy_map_iff_exists_tendsto). So there is y in L with F(z) -> y as z -> x within Z.

4. Definition of g. Let g := extendFrom Z F; that is, g(x) is a chosen limit of F along nhdsWithin x Z whenever such a limit exists. By step 3 and tendsto_extendFrom:
(*) for every x in closure Z, F(z) -> g(x) as z -> x within Z.

5. g is continuous on S. S is contained in closure Z, and by step 3, F has a limit along nhdsWithin x Z at every x in S. Since L is a regular space, continuousOn_extendFrom shows that g is continuous on S.

6. g = F on Z. Let x be in Z, so x is in closure Z.
- For every z in Z, 0 <= ||F z - F x|| <= hsNorm(F z - F x) <= kappa(||z - x||), by (HS1) and the hypothesis.
- The function z -> kappa(||z - x||) is continuous and equals kappa(0) = 0 at z = x. So kappa(||z - x||) -> 0 as z -> x, in particular along nhdsWithin x Z, which is finer than the neighbourhood filter of x.
- By the squeeze theorem (squeeze_zero'), ||F z - F x|| -> 0 along nhdsWithin x Z. That is, F(z) -> F(x) as z -> x within Z (tendsto_iff_norm_sub_tendsto_zero).
- As x is in closure Z and limits in the Hausdorff space L are unique, extendFrom_eq gives g(x) = F(x).

7. Hoelder bound on S. Let x, y be in S. Both nhdsWithin x Z and nhdsWithin y Z are nontrivial, since x and y are in closure Z. Hence the product filter Phi := (nhdsWithin x Z) x (nhdsWithin y Z) on R^n x R^n is nontrivial.
(a) Composing (*) for x and for y with the two projections gives F(p_1) - F(p_2) -> g(x) - g(y) along Phi. So by (HS2), hsNorm(F(p_1) - F(p_2)) -> hsNorm(g(x) - g(y)) along Phi.
(b) Phi is finer than the product of the neighbourhood filters of x and y, which is the neighbourhood filter of (x, y). The map p -> kappa(||p_1 - p_2||) is continuous (step 1). So kappa(||p_1 - p_2||) -> kappa(||x - y||) along Phi.
(c) Z x Z belongs to Phi, and for p in Z x Z the hypothesis gives hsNorm(F(p_1) - F(p_2)) <= kappa(||p_1 - p_2||).
A non-strict inequality that holds eventually passes to limits along a nontrivial filter (le_of_tendsto_of_tendsto). Applied to (a), (b) and (c), this gives hsNorm(g(x) - g(y)) <= kappa(||x - y||) = M (||x - y||/R)^alpha.

8. Steps 5, 6 and 7 show that this g satisfies all three conclusions. No case distinction is needed: if S or Z is empty, the corresponding clauses are vacuous.

## Key steps

1. kappa(t) = M (t/R)^alpha is continuous, nondecreasing on [0, infinity) and kappa(0) = 0, so kappa(2 eta) < epsilon for some eta > 0
2. For x in closure Z, nhdsWithin x Z is nontrivial and its image under F is Cauchy (||.|| <= hsNorm, hypothesis, monotonicity of kappa), hence convergent in the complete space L
3. g := extendFrom Z F satisfies F -> g(x) along nhdsWithin x Z on closure Z and is continuous on S by continuousOn_extendFrom
4. For x in Z, F(z) -> F(x) within Z by the squeeze theorem, so g(x) = F(x) by extendFrom_eq
5. Passing to the limit along (nhdsWithin x Z) x (nhdsWithin y Z) in hsNorm(F p1 - F p2) <= kappa(||p1 - p2||), using continuity of hsNorm and kappa, gives the Hoelder bound on S

## Reference use

### local-project

Queries:
- `sha256sum <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean`
- `python: dag.json nodes by id (selected node, parent graph_campanato-a1, sibling lipschitz_ae_derivative-a1: lean_statement, depends_on, children, status)`
- `python: dag.json lean_statement containing hsNorm / extendFrom / closure / opNorm outside RectifiableVarifold statements (existing generic lemmas, reservations, accepted status)`
- `git show 164f08e449a335e8b0962c8f511579e3e102246a:GMT/Ch05/Submission.lean (layout of accepted Submission.hsNorm_starProjection_trace_identities)`
- `grep -n 'theorem\|lemma' Mathlib/Topology/ExtendFrom.lean`
- `grep -rn 'cauchy_map' Mathlib --include=*.lean`
- `grep -n 'theorem\|lemma' Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `grep -n 'theorem contDiffOn_succ_iff_fderiv_of_isOpen\|theorem contDiffOn_zero' Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `grep -n 'theorem continuousAt_rpow_const' Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `grep -rn 'protected theorem cauchy_iff' Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `grep -rn 'sum_mul_le_sqrt_mul_sqrt|EuclideanSpace.norm_eq|opNorm_le_bound|continuous_rpow_const|rpow_le_rpow|zero_rpow|squeeze_zero''|le_of_tendsto_of_tendsto|mem_closure_iff_nhdsWithin_neBot|HasFDerivAt.fderiv|eq_empty_of_measure_zero|ContinuousOn.congr|measure_mono_null|sdiff_eq_empty' Mathlib`
- `grep -rln 'HolderWith\|HolderOnWith' Mathlib; grep -n 'theorem\|lemma' Mathlib/Topology/MetricSpace/Holder.lean; grep -rn 'extendFrom' Mathlib (no-match search for a closure/dense Hoelder extension lemma)`
- `for nm in allard52_c1h_opNorm_le_hsNorm_continuous allard52_c1h_holder_extension: grep -c nm dag.json; grep -rl nm <run>/nodes GMT <simongmt> <snapshot>/project`
- `runtime.py: _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children (prerequisite_ids = node.children + node.depends_on)`
- `lean src/Submission.lean -o build/GMT/Ch05/Submission.olean (toolchains/lean-4.35.0-rc3-linux; LEAN_PATH = scratch build + lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `lean check/Full.lean; lean check/Types.lean; lean check/Assembly.lean; #print axioms on both children and the parent`
- `python -I scripts/gen.py: lean_contract.validate_lean_statement on both child types; assert Full.lean uses the exact strings; frozen parent and sibling types read from dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-c1-holder-extension-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-c1-holder-extension-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/swarm-project.json`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ExtendFrom.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/ExtendFrom.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ClusterPt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/BooleanAlgebra/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Holder.lean`
- `/tmp/c1h-decomp/check/Full.lean`
- `/tmp/c1h-decomp/check/Types.lean`
- `/tmp/c1h-decomp/check/Assembly.lean`
- `/tmp/c1h-decomp/scripts/gen.py`

Snapshot pins:
- project ea5607598f3133b40a13241f2e51517a8c6423cd;
- Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
The snapshot Submission.lean, the workspace Submission.lean and Contract.lean are identical (sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12).

Mathlib supplies every ingredient but no packaged result:
- extendFrom, tendsto_extendFrom, extendFrom_eq and continuousOn_extendFrom (Topology/ExtendFrom.lean:41,46,50,61);
- Metric.cauchy_iff (MetricSpace/Pseudo/Basic.lean:162);
- cauchy_map_iff_exists_tendsto (UniformSpace/Cauchy.lean:420);
- mem_closure_iff_nhdsWithin_neBot (ClusterPt.lean:265);
- le_of_tendsto_of_tendsto (Order/OrderClosed.lean:472);
- squeeze_zero' (MetricSpace/Pseudo/Lemmas.lean:32);
- Real.continuous_rpow_const (Pow/Continuity.lean:228);
- Real.zero_rpow and Real.rpow_le_rpow (Pow/Real.lean:128,549);
- Real.sum_mul_le_sqrt_mul_sqrt (Analysis/Real/Sqrt.lean:499);
- EuclideanSpace.norm_eq (PiL2.lean:145);
- ContinuousLinearMap.opNorm_le_bound (Normed/Operator/Basic.lean:196);
- IsOpen.eq_empty_of_measure_zero (Measure/OpenPos.lean:86);
- measure_mono_null (OuterMeasure/Basic.lean:54);
- HasFDerivAt.fderiv (FDeriv/Basic.lean:415);
- contDiffOn_zero and contDiffOn_succ_iff_fderiv_of_isOpen (ContDiff/Defs.lean:618,891). The latter carries the extra (n = ω → AnalyticOn) clause;
- ContinuousOn.congr (Topology/ContinuousOn.lean:378).

No-match results:
- No Mathlib lemma extends a Hölder-modulus map continuously from a dense subset. Topology/MetricSpace/Holder.lean has only HolderOnWith.uniformContinuousOn and continuousOn, with edist and ℝ≥0 constants, and no closure or extension result. extendFrom is otherwise used only in Topology/Order/ExtendFrom.lean and Rolle.lean.
- The DAG has no node for this extension lemma.
- ||A|| <= hsNorm A occurs as a conjunct of the accepted hsNorm_starProjection_trace_identities and aal_l1th_projection_algebra. Both bundle unrelated projection/trace identities and lack continuity, so their types differ.
- arp_opNorm_le_hsNorm, allard52_gpa_hsNorm_bounds, any_radius_gr_linear_algebra_basics and lgc_hsNormSq_bounds are unaccepted nodes of other parents and cannot be shared.
- Neither proposed name occurs in dag.json, node artifacts, GMT/, SimonGMT or the snapshot.

Runtime: a node's prerequisites are node.children plus node.depends_on (runtime.py _overlay_accepted_children). The parent can therefore cite the sibling allard52_lipschitz_hasFDerivAt_of_ae, but its children cannot.

Lean checks against a scratch build of the frozen GMT.Ch05.Submission olean:
- Full.lean proves both children; their only axioms are propext, Classical.choice and Quot.sound.
- Full.lean also proves the exact frozen parent type from the two children plus the sibling's exact frozen type. The sibling's sorry is the only sorryAx.
- Types.lean and Assembly.lean, generated from the exact submitted strings, compile with only the input-sorry warnings.
- validate_lean_statement accepts both child types.
