# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_campanato-a1`
- Child DAG node: `root.allard_regularity-a1.graph_campanato-a1.campanato_center_holder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (the Hoelder argument after book (11): midpoint averaging of two Campanato bounds). The parent's computation never uses that x_1, x_2 are Lebesgue points, so it is stated here for all pairs in B^o_{R/16}(0). The constant uses v_n := L^n(B_1(0)), which equals omega_n; its explicit Gamma-function value is not needed.

Notation. hsNormSq(T) := sum_{i<m} ||T e_i||^2, hsNorm := sqrt(hsNormSq); balls B_t(.) are closed, B^o_t(.) open; L^n is Lebesgue measure on R^n and integral^- the lower Lebesgue integral. (Camp): for every z in B_{R/4}(0) and 0 < s <= R/4, integral^-_{B_{s/2}(z)} ofReal(hsNormSq(G(x) - c(z))) dx <= ofReal(A s^n (s/R)^(2 alpha)).

1. Constant. v_n := L^n(B_1(0)) is positive and finite, and L^n(B_t(w)) = t^n v_n for all w and t >= 0 (Measure.addHaar_closedBall', finrank R^n = n). Put C := (2^(2n+4)/v_n)^(1/2) >= 0. C depends only on n.

2. Hilbert-Schmidt facts. hsNormSq(T) >= 0 and hsNormSq(0) = 0; hsNormSq(T - T') <= 2 hsNormSq(T) + 2 hsNormSq(T') (sum ||a - b||^2 <= 2||a||^2 + 2||b||^2 over a = T e_i, b = T' e_i); T -> hsNormSq(T - T0) is continuous, so x -> hsNormSq(G(x) - T0) is measurable for fixed T0.

Now let m, k, G, c, A >= 0, R > 0, 0 < alpha <= 1 with G measurable and (Camp), and let x, y be in B^o_{R/16}(0).

3. The case x = y. Then hsNorm(c(x) - c(y)) = hsNorm(0) = 0, and C sqrt(A) (0/R)^alpha = 0 because alpha > 0. The inequality holds.

4. Geometry for x != y. Put d := ||x - y||, so 0 < d <= ||x|| + ||y|| < R/8, s := 2d (so 0 < s < R/4 and s/2 = d), m0 := (x + y)/2 and B' := B_{d/2}(m0). For w in B', ||w - x|| <= ||w - m0|| + ||m0 - x|| <= d/2 + d/2 = d, and likewise ||w - y|| <= d; so B' is contained in B_d(x) cap B_d(y) = B_{s/2}(x) cap B_{s/2}(y). Also x, y lie in B_{R/4}(0), so (Camp) applies at z = x and z = y with this s.

5. Pointwise bound. For every w, c(x) - c(y) = (G(w) - c(y)) - (G(w) - c(x)), so by step 2
 hsNormSq(c(x) - c(y)) <= 2 hsNormSq(G(w) - c(x)) + 2 hsNormSq(G(w) - c(y)).

6. Averaging. Apply ofReal and integrate over B' (lower integral; the two integrands on the right are measurable, so the lower integral is additive; the integral of a constant over B' is the constant times L^n(B')), then enlarge the domains (monotonicity of the lower integral in the set) and use (Camp) at x and at y:
 ofReal(hsNormSq(c(x) - c(y))) L^n(B') <= 2 integral^-_{B'} ofReal(hsNormSq(G(w) - c(x))) dw + 2 integral^-_{B'} ofReal(hsNormSq(G(w) - c(y))) dw
 <= 2 integral^-_{B_{s/2}(x)} ofReal(hsNormSq(G(w) - c(x))) dw + 2 integral^-_{B_{s/2}(y)} ofReal(hsNormSq(G(w) - c(y))) dw
 <= 4 ofReal(A s^n (s/R)^(2 alpha)).

7. Arithmetic. L^n(B') = (d/2)^n v_n is positive and finite; dividing and passing to real numbers (A >= 0):
 hsNormSq(c(x) - c(y)) <= 4 A (2d)^n (2d/R)^(2 alpha) / ((d/2)^n v_n).
 Now (2d)^n/(d/2)^n = 4^n, and (2d/R)^(2 alpha) = 2^(2 alpha) (d/R)^(2 alpha) (Real.mul_rpow with nonnegative factors), and 2^(2 alpha) <= 2^2 = 4 because 0 < 2 alpha <= 2 and the base 2 is >= 1. Hence
 hsNormSq(c(x) - c(y)) <= 4^(n+2) A (d/R)^(2 alpha) / v_n = C^2 A ((d/R)^alpha)^2,
 using 4^(n+2) = 2^(2n+4) and (d/R)^(2 alpha) = ((d/R)^alpha)^2 (d/R >= 0, Real.rpow_mul / rpow_natCast).

8. Square roots. All factors are nonnegative, so taking square roots (Real.sqrt_le_sqrt, sqrt of a product of nonnegative numbers, sqrt(u^2) = u for u >= 0):
 hsNorm(c(x) - c(y)) = sqrt(hsNormSq(c(x) - c(y))) <= C sqrt(A) (||x - y||/R)^alpha.
 Together with step 3 this proves the claim for all x, y in B^o_{R/16}(0), with C depending only on n.

## Key steps

1. C := (2^(2n+4)/v_n)^(1/2), v_n the Lebesgue measure of the closed unit ball, L^n(B_t(w)) = t^n v_n
2. For x != y with d = |x - y| < R/8, the ball B_{d/2}((x+y)/2) lies in B_d(x) cap B_d(y)
3. Pointwise hsNormSq(c(x) - c(y)) <= 2 hsNormSq(G - c(x)) + 2 hsNormSq(G - c(y)); average over the midpoint ball and use the Campanato bound with s = 2d at x and at y
4. Arithmetic 4 * 4^n * 2^(2 alpha) <= 2^(2n+4) and square roots give hsNorm(c(x) - c(y)) <= C sqrt(A)(d/R)^alpha

## Reference use

### local-project

Queries:
- `sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `rg -n 'AbsolutelyContinuousOnInterval' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem .*integral_deriv|theorem .*integral_eq_sub_of' Mathlib/MeasureTheory/Integral/IntervalIntegral Mathlib/MeasureTheory/Function`
- `rg -n 'const_of_ae_hasDerivAt_zero|theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval' Mathlib`
- `rg -n 'theorem ae_tendsto_average_norm_sub' Mathlib/MeasureTheory/Covering/DensityTheorem.lean; rg -n 'isUnifLocDoublingMeasure' Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n 'theorem addHaar_closedBall|theorem measure_prod_null|theorem prod_apply_symm|theorem exists_measurable_superset_of_null|measure_preimage_add_right|finrank_euclideanSpace' Mathlib`
- `rg -n 'ae_differentiableWithinAt_of_mem' Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n 'norm_fderiv_le_of_lipschitzOn|range_starProjection|starProjection_norm_le|contDiffOn_succ_iff_fderiv_of_isOpen|ContDiffOn.continuousOn_fderiv_of_isOpen|contDiffOn_zero|eqOn_open_of_ae_eq|continuousOn_extendFrom|extendFrom_eq|integral_hasDerivAt_right|measurable_fderiv|instBorelSpace|integrableOn_of_bounded|Integrable.of_bound|continuousAt_rpow_const|ofReal_integral_eq_lintegral_ofReal|withDensity_apply|restrict_restrict|setLIntegral_le_lintegral|lintegral_indicator|setLIntegral_congr_fun|lintegral_add_left|continuous_parametric_intervalIntegral_of_continuous' Mathlib`
- `python: scan dag.json lean_name / lean_statement fields (name reservation; existing Campanato, C^1-criterion and graph lemmas; sibling frozen types)`
- `for nm in <5 proposed names>: grep -c nm dag.json; rg -l nm <snapshot>; grep -rl nm GMT .lake/packages/simongmt; grep -rl nm <run>/nodes`
- `grep -n max_nodes /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py swarm-project.json .humanize/swarm-configs/bbb8844778a24d338c1a9c1f12b469ef.json; sed -n 3160,3165p runtime.py (prerequisites = node.children + node.depends_on)`
- `lean src/Submission.lean -o build/GMT/Ch05/Submission.olean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = scratch build + lake-packages-25730c7c)`
- `lean check/Types.lean (import GMT.Ch05.Submission; five child types as sorry'd theorems)`
- `lean check/Assembly.lean (parent frozen type proved from the five child types and the frozen types of allard52_tangent_ae, allard52_graph_plane_algebra, allard52_graph_comparison as sorry'd theorems)`
- `python: lean_contract.validate_lean_statement on the five child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ExtendFrom.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-campanato-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/bbb8844778a24d338c1a9c1f12b469ef.json`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/lean_contract.py`
- `/tmp/gc-decomp-F9oKFQ/check/Types.lean`
- `/tmp/gc-decomp-F9oKFQ/check/Assembly.lean`

Snapshot pins: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean, Contract.lean and the snapshot Submission.lean are identical (sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12).

Usable Mathlib lemmas (snapshot paths):
- AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero (vector-valued; AbsolutelyContinuousFun.lean:169) and integral_deriv_eq_sub (:225);
- LipschitzOnWith.absolutelyContinuousOnInterval (Function/AbsolutelyContinuous.lean:309);
- IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (DensityTheorem.lean:150), with instance isUnifLocDoublingMeasureOfIsAddHaarMeasure (EqHaar.lean:550);
- Measure.addHaar_closedBall' (EqHaar.lean:475);
- measure_prod_null and prod_apply_symm (Measure/Prod.lean:401,706);
- exists_measurable_superset_of_null (MeasureSpaceDef.lean:219);
- LipschitzOnWith.ae_differentiableWithinAt_of_mem (Rademacher.lean:361);
- norm_fderiv_le_of_lipschitzOn (FDeriv/Basic.lean:939);
- measurable_fderiv (FDeriv/Measurable.lean:378), with ContinuousLinearMap.instBorelSpace;
- Submodule.range_starProjection and starProjection_norm_le (Projection/Basic.lean:302,386);
- contDiffOn_succ_iff_fderiv_of_isOpen, ContDiffOn.continuousOn_fderiv_of_isOpen and contDiffOn_zero (ContDiff/Defs.lean:891,916,618);
- Measure.eqOn_open_of_ae_eq (OpenPos.lean:115);
- extendFrom_eq and continuousOn_extendFrom (ExtendFrom.lean:50,61);
- intervalIntegral.integral_hasDerivAt_right (FundThmCalculus.lean:725);
- Measure.integrableOn_of_bounded (IntegrableOn.lean:716);
- Real.continuousAt_rpow_const, whose hypothesis is x != 0 or 0 <= q (Pow/Continuity.lean:220).

Other findings:
- The omega_n formula is outside the import closure, so the children use v_n = L^n(B_1(0)) with Haar scaling.
- Mathlib, SimonGMT and the DAG contain no usable Campanato lemma, Lipschitz C^1 criterion or line-wise FTC. The accepted any_radius_campanato needs ContinuousOn g, which is the thing to be proved here.
- None of the five proposed bare names occurs in dag.json (214 reserved names), node artifacts, GMT/, SimonGMT or the snapshot.
- Prerequisites are node.children plus node.depends_on (runtime.py:3162), so the children cannot cite the parent's siblings; child 1 takes their conclusions as hypotheses.
- Running params: max_nodes 1000, and the DAG has 200 nodes.

Lean checks:
- Types.lean and Assembly.lean compile against the frozen Submission olean.
- Assembly proves the exact frozen parent type from the five child types and the three sibling types; only the 8 input sorry warnings appear.
- validate_lean_statement accepts all five types.
