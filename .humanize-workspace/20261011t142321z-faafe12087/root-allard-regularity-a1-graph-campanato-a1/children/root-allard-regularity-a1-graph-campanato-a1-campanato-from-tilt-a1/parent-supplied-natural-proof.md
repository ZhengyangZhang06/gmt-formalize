# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_campanato-a1`
- Child DAG node: `root.allard_regularity-a1.graph_campanato-a1.campanato_from_tilt-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (Simon Ch. 5, proof of 5.2, (10)-(11)), with the graph-comparison inequality (sibling allard52_graph_comparison of the parent) and the a.e. measurability of the tangent map (sibling allard52_tangent_ae of the parent) taken as the explicit hypotheses (vi) and (v). The integrability bound uses the operator norm (|p_w - P|^2 <= 4(n+l)) instead of the rank, so no dimension information about S is needed.

Hypotheses (as in the statement): (i) the closed ball B_R(0) of R^(n+l) is contained in U; (ii) f(0) = 0; (iii) f is 1-Lipschitz on the closed ball B^n_R(0); (iv) spt V cap B_R(0) = q(graphOver f (B^n_R(0))) cap B_R(0); (v) w -> V.tangentProj w is V.weight-a.e. strongly measurable; (vi) for every Phi : R^(n+l) -> L(R^(n+l)) -> [0, infinity] with uncurry Phi measurable and every measurable D contained in the open ball B^o_{R/2}(0) of R^n, integral^-_D Phi(F(x), G(x)) dx <= integral^-_{q(graphOver f D)} Phi(y, p_y) dmu(y); (vii) V.tiltExcess zeta s (S zeta) <= A (s/R)^e for all zeta in spt V cap B_{R/2}(0) and 0 < s <= R/2. Here R > 0 and A, e are arbitrary reals.

Notation. mu := V.weight, p_w := V.tangentProj w, F(x) := q(graphPoint x (f x)), Df(x) := fderiv f x, G(x) := starProjection of (span{graphPoint v (Df(x) v)}).map q, hsNormSq(T) := sum_i ||T e_i||^2 (e_i the standard basis vectors of the domain), ||.|| the Euclidean/operator norm. All balls B_t(.) are closed, B^o_t(.) open; integral^- denotes the lower Lebesgue integral (lintegral).

1. Elementary facts.
 (a) graphPoint is linear: graphPoint x y - graphPoint x' y' = graphPoint (x - x') (y - y'), and ||graphPoint x y||^2 = ||x||^2 + ||y||^2. Indeed the coordinates of graphPoint x y are those of x followed by those of y (Fin.append), and the squared Euclidean norm is the sum of squared coordinates; split the sum over Fin (n + l) into the first n and the last l indices (Fin.sum_univ_add, Fin.append_left, Fin.append_right).
 (b) For x, x' in B^n_R(0): ||F(x) - F(x')|| = ||graphPoint (x - x') (f x - f x')|| (q is a linear isometry and (a)) = (||x - x'||^2 + ||f x - f x'||^2)^(1/2) <= sqrt(2) ||x - x'||, because f is 1-Lipschitz on B^n_R(0) (iii).
 (c) F(0) = q(graphPoint 0 0) = 0 by (ii), so (b) with x' = 0 gives ||F(x)|| <= sqrt(2) ||x|| for x in B^n_R(0).
 (d) For every continuous linear T of R^(n+l): hsNormSq(T) = sum_i ||T e_i||^2 <= (n + l) ||T||^2, since ||T e_i|| <= ||T|| ||e_i|| = ||T||. Every orthogonal projection P_W = W.starProjection has ||P_W|| <= 1 (Submodule.starProjection_norm_le), and by its definition V.tangentProj w is either such a projection or 0, so ||p_w|| <= 1 for every w. Hence for every subspace Q: 0 <= hsNormSq(p_w - Q.starProjection) <= (n + l)(||p_w|| + ||Q.starProjection||)^2 <= 4(n + l).
 (e) T -> hsNormSq(T - P) is continuous for each fixed P (finite sum of squared norms of the continuous evaluations T -> (T - P) e_i).

2. Fix z in B^n_{R/4}(0) and 0 < s <= R/4. Put zeta := F(z), Q := S(zeta), P := Q.starProjection, D := B^n_{s/2}(z) (a closed, hence measurable, subset of R^n) and B := B_s(zeta) (closed ball of R^(n+l)).
 (a) zeta lies in spt V cap B_{R/2}(0): by 1(c), ||zeta|| <= sqrt(2) ||z|| <= sqrt(2) R/4 < R/2 <= R. Since ||z|| <= R/4 <= R, zeta = q(graphPoint z (f z)) belongs to q(graphOver f (B^n_R(0))), and also to B_R(0); by (iv), zeta is in spt V cap B_R(0), so zeta is in spt V, and with ||zeta|| <= R/2 we get zeta in spt V cap B_{R/2}(0).
 (b) D is contained in B^o_{R/2}(0): for x in D, ||x|| <= ||z|| + s/2 <= R/4 + R/8 = 3R/8 < R/2. In particular D is contained in B^n_R(0).
 (c) B is contained in B_R(0), hence in U by (i): for y in B, ||y|| <= ||zeta|| + s <= sqrt(2) R/4 + R/4 < R. B is compact (closed and bounded in a finite-dimensional space).

3. mu(B) < infinity. By definition mu = (H^n restricted to M).withDensity(ofReal o theta). Since B is measurable, mu(B) = integral^-_B ofReal(theta) d(H^n restricted to M) = integral^-_{M cap B} ofReal(theta) dH^n (withDensity_apply and Measure.restrict_restrict). By the structure field integrableOn_mult applied to the compact set B contained in U (step 2(c)), theta is H^n-integrable on M cap B, so integral^-_{M cap B} ofReal(theta) dH^n <= integral^-_{M cap B} ||theta||_e dH^n < infinity.

4. Integrability and Bochner form. Let h(y) := hsNormSq(p_y - P). By (v) and 1(e), h is mu-a.e. strongly measurable (continuous function of an a.e. strongly measurable map), and 0 <= h <= 4(n + l) by 1(d). As mu(B) < infinity (step 3), h is mu-integrable on B (a bounded a.e. strongly measurable function on a finite-measure set: Measure.integrableOn_of_bounded with mu(B) != infinity, or Integrable.of_bound for the finite measure mu restricted to B). Hence (ofReal_integral_eq_lintegral_ofReal) integral^-_B ofReal(h) dmu = ofReal(integral_B h dmu).

5. Tilt bound. By definition, V.tiltExcess zeta s Q = (s^n)^(-1) integral_B h dmu, and s^n > 0, so integral_B h dmu = s^n V.tiltExcess zeta s Q. By step 2(a) and 0 < s <= R/4 <= R/2, hypothesis (vii) gives V.tiltExcess zeta s Q <= A (s/R)^e; multiplying by s^n > 0: integral_B h dmu <= A s^n (s/R)^e. With step 4: integral^-_B ofReal(h) dmu <= ofReal(A s^n (s/R)^e).

6. Comparison. Define Phi(w, T) := indicator_B(w) * ofReal(hsNormSq(T - P)) (value in [0, infinity]). It is jointly measurable: (w, T) -> indicator_B(w) is measurable (B closed, composition with the measurable first projection), (w, T) -> ofReal(hsNormSq(T - P)) is measurable (continuous function of the measurable second projection, 1(e)), and products of measurable [0, infinity]-valued functions are measurable. D is measurable and contained in B^o_{R/2}(0) (step 2(b)), so hypothesis (vi) gives
 integral^-_D Phi(F(x), G(x)) dx <= integral^-_{q(graphOver f D)} Phi(y, p_y) dmu(y).
 (a) Left side. For x in D, x and z lie in B^n_R(0), so by 1(b) ||F(x) - zeta|| <= sqrt(2) ||x - z|| <= sqrt(2) s/2 < s; thus F(x) is in B and Phi(F(x), G(x)) = ofReal(hsNormSq(G(x) - P)). As D is measurable, the left side equals integral^-_D ofReal(hsNormSq(G(x) - P)) dx (setLIntegral_congr_fun).
 (b) Right side. Restricting the measure to the set q(graphOver f D) can only decrease the lower integral of a nonnegative function (setLIntegral_le_lintegral), and integral^- indicator_B(y) ofReal(h(y)) dmu(y) = integral^-_B ofReal(h) dmu (lintegral_indicator, B measurable). So the right side is <= integral^-_B ofReal(h) dmu.

7. Conclusion. Combining steps 6 and 5:
 integral^-_{B^n_{s/2}(z)} ofReal(hsNormSq(G(x) - (S(F(z))).starProjection)) dx <= integral^-_B ofReal(h) dmu <= ofReal(A s^n (s/R)^e).
 Since z in B^n_{R/4}(0) and s in (0, R/4] were arbitrary, the theorem follows.

## Key steps

1. Graph geometry: |F(x) - F(x')| <= sqrt(2)|x - x'| on B^n_R(0), |F(x)| <= sqrt(2)|x|, and 0 <= hsNormSq(p_w - P) <= 4(n+l) via operator norms of projections
2. zeta = F(z) lies in spt V cap B_{R/2}(0); D = B^n_{s/2}(z) lies in B^o_{R/2}(0); B_s(zeta) is a compact subset of B_R(0), hence of U
3. mu(B_s(zeta)) < infinity from integrableOn_mult; the bounded a.e. strongly measurable integrand is integrable, so its lintegral is ofReal(s^n E(zeta, s, S zeta)) <= ofReal(A s^n (s/R)^e)
4. Apply the comparison hypothesis to Phi(w, T) = 1_{B_s(zeta)}(w) ofReal(hsNormSq(T - P)): the indicator is 1 along F(D) and the right side is at most the lintegral over B_s(zeta)

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
