# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1`
- Child DAG node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.line_integral_rep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is steps 0-3 of the parent proof, with an open convex set U in place of the ball B^o_r(c). It uses three sibling results:
 [segment_null] For every L^n-null N ⊆ R^n and x, h ∈ R^n: for L^n-a.e. w, L^1({t : x + w + t h ∈ N}) = 0.
 [lipschitz_ftc] Suppose a <= b, phi is Lipschitz on [a, b], k is continuous on [a, b], and phi has derivative k(t) at a.e. t ∈ (a, b). Then phi(b) - phi(a) = integral_a^b k.
 [segment_integral_continuous] If U is open and convex and g is continuous on U, then I(a, b) := integral_0^1 g(a + tau(b - a))(b - a) dtau is continuous on U x U.

0. The bad set. Let N0 := {p ∈ R^n : not (p ∈ U => f has Frechet derivative g(p) at p)}. Equivalently, N0 = {p ∈ U : f does not have derivative g(p) at p}. The hypothesis "for a.e. x, x ∈ U => HasFDerivAt f (g x) x" says exactly L^n(N0) = 0 (ae_iff). If p ∈ U and p ∉ N0, then f has derivative g(p) at p.

1. Setup. Fix x, y ∈ U and put h := y - x. U is open, so there are rho1, rho2 > 0 with B^o_rho1(x) ⊆ U and B^o_rho2(y) ⊆ U. Let rho := min(rho1, rho2) > 0. Then B^o_rho(x) ⊆ U and B^o_rho(y) ⊆ U. For every w ∈ B^o_rho(0), ||(x + w) - x|| = ||w|| < rho, so x + w ∈ U; likewise y + w ∈ U. Also, for a, b ∈ U and tau ∈ [0, 1], a + tau(b - a) = (1 - tau)a + tau b ∈ U by convexity.
Let I be as in [segment_integral_continuous], and define F(w) := f(y + w) - f(x + w) - I(x + w, y + w) for w ∈ R^n. Since F(0) = f(y) - f(x) - integral_0^1 g(x + tau(y - x))(y - x) dtau, the goal is F(0) = 0.

2. F vanishes at every good w. Claim: if w ∈ B^o_rho(0) and L^1({t ∈ R : x + w + t h ∈ N0}) = 0, then F(w) = 0.
Proof of the claim. Put sigma(t) := x + w + t h. Since (y + w) - (x + w) = h, sigma(t) = (x + w) + t((y + w) - (x + w)). As x + w and y + w lie in U, step 1 gives sigma(t) ∈ U for every t ∈ [0, 1].
 (a) phi(t) := f(sigma(t)) is (K||h||)-Lipschitz on [0, 1]. For t, t' ∈ [0, 1], both sigma(t) and sigma(t') lie in U, so
 ||phi(t) - phi(t')|| <= K||sigma(t) - sigma(t')|| = K||(t - t')h|| = K||h|| |t - t'|.
 (b) k(t) := g(sigma(t)) h is continuous on [0, 1]. g is continuous on U, sigma is continuous and maps [0, 1] into U, and evaluation at the fixed vector h is continuous (ContinuousOn.comp, ContinuousOn.clm_apply).
 (c) For a.e. t ∈ (0, 1), phi has derivative k(t) at t. The hypothesis L^1({t : sigma(t) ∈ N0}) = 0 means sigma(t) ∉ N0 for a.e. t (ae_iff). Take such a t with t ∈ (0, 1). Then sigma(t) ∈ U and sigma(t) ∉ N0, so f has Frechet derivative g(sigma(t)) at sigma(t) by step 0. The affine map sigma has derivative h at t: t |-> t h has derivative h, and adding a constant does not change it. By the chain rule (HasFDerivAt.comp_hasDerivAt), phi = f o sigma has derivative g(sigma(t)) h = k(t) at t.
 (d) Apply [lipschitz_ftc] with a = 0, b = 1, Lipschitz constant K||h||, the curve phi and the continuous function k. This gives phi(1) - phi(0) = integral_0^1 k(tau) dtau. Here phi(1) = f(x + w + h) = f(y + w) and phi(0) = f(x + w). Also
 integral_0^1 k(tau) dtau = integral_0^1 g(x + w + tau h) h dtau = integral_0^1 g((x + w) + tau((y + w) - (x + w)))((y + w) - (x + w)) dtau = I(x + w, y + w).
Hence f(y + w) - f(x + w) = I(x + w, y + w), that is, F(w) = 0.

3. F = 0 almost everywhere on B^o_rho(0). Apply [segment_null] to the null set N0, the point x and the direction h: for L^n-a.e. w, L^1({t : x + w + t h ∈ N0}) = 0. By step 2, for L^n-a.e. w: w ∈ B^o_rho(0) => F(w) = 0. The ball is measurable, so this says F = 0 almost everywhere for L^n restricted to B^o_rho(0) (ae_restrict_iff').

4. F is continuous on B^o_rho(0). f is continuous on U, because a map that is Lipschitz on U is continuous on U (LipschitzOnWith.continuousOn). The maps w |-> y + w and w |-> x + w are continuous and send B^o_rho(0) into U (step 1). So w |-> f(y + w) and w |-> f(x + w) are continuous on B^o_rho(0). By [segment_integral_continuous] (U open and convex, g continuous on U), I is continuous on U x U. The continuous map w |-> (x + w, y + w) sends B^o_rho(0) into U x U, so w |-> I(x + w, y + w) is continuous on B^o_rho(0). Differences of continuous maps are continuous, so F is continuous on B^o_rho(0).

5. F vanishes on the whole ball, in particular at 0. Let Z := {w ∈ B^o_rho(0) : F(w) ≠ 0}. Z is open, because F is continuous on the open ball and {v : v ≠ 0} is open. Z is L^n-null by step 3. Lebesgue measure gives positive measure to every nonempty open set, so Z is empty. In Lean this is Measure.eqOn_open_of_ae_eq, applied to the open ball, the continuous maps F and 0, and Lebesgue measure (an IsOpenPosMeasure). Since rho > 0, 0 ∈ B^o_rho(0), so F(0) = 0, that is,
 f(y) - f(x) = I(x, y) = integral_0^1 g(x + tau(y - x))(y - x) dtau.
Since x and y were arbitrary points of U, the formula holds for all x, y ∈ U.

## Key steps

1. N0 := {p ∈ U : not HasFDerivAt f (g p) p} is L^n-null (ae_iff)
2. Fix x, y ∈ U, h = y - x and rho > 0 with B_rho(x), B_rho(y) ⊆ U; define F(w) := f(y + w) - f(x + w) - I(x + w, y + w)
3. If w ∈ B_rho(0) and its segment meets N0 in an L^1-null set: t |-> f(x + w + t h) is K||h||-Lipschitz on [0,1] with a.e. derivative g(x + w + t h)h (chain rule), so lipschitz_ftc gives F(w) = 0
4. segment_null: F = 0 a.e. on B_rho(0)
5. F is continuous on B_rho(0) (f Lipschitz; segment_integral_continuous); a continuous function that is a.e. zero on an open set vanishes there (Measure.eqOn_open_of_ae_eq), so F(0) = 0

## Reference use

### local-project

Queries:
- `sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `grep -n 'theorem\|lemma' mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `grep -n '^theorem\|^lemma\|^def' mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `rg -n 'theorem (integral_hasDerivAt_right|measure_prod_null|prod_apply_symm|eqOn_open_of_ae_eq|continuousAt_of_dominated_interval|continuousWithinAt_of_dominated_interval|norm_integral_le_of_norm_le_const|exists_cthickening_subset_open|hasFDerivAt_iff_isLittleO_nhds_zero|exists_measurable_superset_of_null|measure_preimage_add_right|continuous_parametric_intervalIntegral_of_continuous|comp_hasDerivAt)\b' mathlib/Mathlib`
- `rg -n 'theorem (integral_interval_sub_left|Ioo_ae_eq_Icc|ae_ne|stronglyMeasurableAtFilter)\b' mathlib/Mathlib`
- `rg -n 'LipschitzOnWith' mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `grep -rn 'IsCompact.cthickening\|theorem mem_cthickening_of_dist_le' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `grep -rn 'theorem ContinuousOn.clm_apply\|theorem ContinuousAt.clm_apply' mathlib/Mathlib/Analysis/Normed/Operator`
- `python: scan dag.json lean_name / lean_statement for intervalIntegral|HasDerivAt|AbsolutelyContinuous|LipschitzOnWith|volume {t (reuse and name reservation)`
- `grep -rl allard52_lad_ <run>/nodes GMT <simongmt> <snapshot>; git show <each of 1216 run branches>:GMT/Ch05/Submission.lean | grep allard52_lad_`
- `git show <run branches>:GMT/Ch05/Submission.lean | grep '^import' (precedent for extra Mathlib imports, e.g. accepted root-affine-approximation-a1-l1-tilt-height-a1)`
- `lean src/Submission.lean -o build/GMT/Ch05/Submission.olean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = scratch build + lake-packages-25730c7c)`
- `lean check/Types2.lean; lean check/Assembly2.lean; lean check/Full.lean; lean check/Inst.lean`
- `python: lean_contract.validate_lean_statement on the five child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-lipschitz-ae-derivative-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-lipschitz-ae-derivative-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-c1-holder-extension-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/lean_contract.py`
- `/tmp/lad-decomp/check/Types2.lean`
- `/tmp/lad-decomp/check/Assembly2.lean`
- `/tmp/lad-decomp/check/Full.lean`
- `/tmp/lad-decomp/check/Inst.lean`

Snapshot pins: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean, Contract.lean and the snapshot Submission.lean are identical (sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12).

Usable Mathlib lemmas (snapshot paths):
- AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero (AbsolutelyContinuousFun.lean:169) is valid for normed-space values. integral_deriv_eq_sub (:225) is real-valued only, so the R^l-valued FTC (lipschitz_ftc) is a genuine obligation.
- LipschitzOnWith.absolutelyContinuousOnInterval (Function/AbsolutelyContinuous.lean:309).
- LipschitzOnWith.div / to_additive sub (Normed/Group/Uniform.lean:327).
- intervalIntegral.continuousAt_of_dominated_interval (DominatedConvergence.lean:280). continuous_parametric_intervalIntegral_of_continuous (:613) needs global continuity, so it does not apply.
- Measure.measure_prod_null and prod_apply_symm (Measure/Prod.lean:401, 706).
- exists_measurable_superset_of_null (MeasureSpaceDef.lean:219).
- Measure.eqOn_open_of_ae_eq (OpenPos.lean:115).
- Ioo_ae_eq_Icc (NullSingletonClass.lean:122).
- intervalIntegral.integral_hasDerivAt_right (FundThmCalculus.lean:725).
- intervalIntegral.norm_integral_le_of_norm_le_const and integral_interval_sub_left (IntervalIntegral/Basic.lean:769, 1121).
- hasFDerivAt_iff_isLittleO_nhds_zero (FDeriv/Basic.lean:815).
- HasFDerivAt.comp_hasDerivAt (Deriv/Comp.lean:374).
- IsCompact.exists_cthickening_subset_open, IsCompact.cthickening and mem_cthickening_of_dist_le (Thickening.lean:426, 283, 201).
- ContinuousOn/ContinuousAt.clm_apply (BoundedLinearMaps.lean:476, 482).

What is missing: Mathlib, SimonGMT and the DAG contain no line-wise Fubini lemma, no vector-valued Lipschitz FTC, no segment-integral continuity lemma and no differentiability-from-mean-value criterion. Nothing can be reused.

The AbsolutelyContinuousFun module is outside the frozen import closure. Accepted branches already add Mathlib imports to Submission.lean, so lipschitz_ftc may add it.

Names: none of the five proposed names (or the prefix allard52_lad_) occurs in dag.json (361 names), node artifacts, GMT/, SimonGMT, the snapshot, or Submission.lean on any of 1216 run branches.

Lean checks:
- Types2.lean and Assembly2.lean compile against the frozen olean. Assembly proves the exact frozen parent type from the five child types.
- Full.lean proves all five children and the parent with axioms [propext, Classical.choice, Quot.sound] only.
- Inst.lean confirms the standard instances.
- validate_lean_statement accepts all five types.
