# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1.l1_tilt_height-a1`
- Child DAG node: `root.affine_approximation-a1.l1_tilt_height-a1.cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the cutoff of step 1 of the supplied proof (Simon, Ch. 5, proof of Lemma 2.1, p. 108: "choosing zeta = 1 in B_{rho/2}(0), zeta = 0 outside B_rho(0) and |grad zeta| <= 3/rho"). The supplied proof only asserts that a C^1 profile phi with |phi'| <= 3 exists; here it is constructed explicitly.

Notation: R^m = Rn m = EuclideanSpace R (Fin m) with the Euclidean norm; S := Real.smoothTransition. (Every Mathlib fact cited below is available from the contract's imports.) Mathlib (Analysis/SpecialFunctions/SmoothTransition.lean) gives: S is C^infinity (Real.smoothTransition.contDiff); 0 <= S <= 1 (nonneg, le_one); S(s) = 0 for s <= 0 (zero_of_nonpos); S(s) = 1 for s >= 1 (one_of_one_le).

1. The bump g. Define g : R -> R by g(t) := S(12(t - 1/2)) * S(12(1 - t)).
 (a) g is C^infinity (products and compositions of C^infinity maps with affine maps); in particular g is continuous.
 (b) 0 <= g <= 1, since both factors lie in [0, 1].
 (c) g(t) = 0 if t <= 1/2 (then 12(t - 1/2) <= 0, so the first factor is 0), and g(t) = 0 if t >= 1 (then 12(1 - t) <= 0, so the second factor is 0).
 (d) g(t) = 1 if 7/12 <= t <= 11/12, because then 12(t - 1/2) >= 1 and 12(1 - t) >= 1, so both factors equal 1.

2. The constant c := integral_{1/2}^{1} g(s) ds. By additivity of the interval integral,
 c = integral_{1/2}^{7/12} g + integral_{7/12}^{11/12} g + integral_{11/12}^{1} g.
 The first and third integrals are >= 0 since g >= 0 and the bounds are ordered, and the middle one equals integral_{7/12}^{11/12} 1 ds = 1/3 by 1(d). Hence c >= 1/3 > 0 and 0 < c^{-1} <= 3. (In fact c = 5/12, but only c >= 1/3 is used.)

3. The profile phi : R -> R, phi(t) := 1 - c^{-1} integral_{1/2}^{t} g(s) ds.
 (a) Since g is continuous, the fundamental theorem of calculus (intervalIntegral.integral_hasDerivAt_right, or Continuous.integral_hasStrictDerivAt) gives HasDerivAt phi (-c^{-1} g(t)) t for every t. So phi is differentiable and deriv phi = -c^{-1} g, which is continuous; hence phi is C^1 (contDiff_one_iff_deriv).
 (b) |deriv phi (t)| = c^{-1} g(t) <= c^{-1} <= 3 for all t, so by the mean value theorem (lipschitzWith_of_nnnorm_deriv_le) phi is 3-Lipschitz: |phi(s) - phi(t)| <= 3|s - t|.
 (c) If t <= 1/2, then g = 0 on [t, 1/2] by 1(c), so integral_{1/2}^{t} g = -integral_{t}^{1/2} g = 0 and phi(t) = 1.
 (d) If t >= 1, then g = 0 on [1, t] by 1(c), so integral_{1/2}^{t} g = integral_{1/2}^{1} g + integral_{1}^{t} g = c + 0, and phi(t) = 1 - c^{-1} c = 0.
 (e) If 1/2 <= t <= 1, then, since g >= 0, 0 <= integral_{1/2}^{t} g <= integral_{1/2}^{1} g = c, so 0 <= phi(t) <= 1. Together with (c) and (d): 0 <= phi(t) <= 1 for every real t.

4. Definition of zeta. Given m, xi in R^m and rho > 0, define zeta(x) := phi(||x - xi|| / rho).
 (a) 0 <= zeta(x) <= 1 for every x, by 3(e).
 (b) If x lies in the closed ball B_{rho/2}(xi), then ||x - xi|| / rho <= 1/2, so zeta(x) = 1 by 3(c).
 (c) If rho <= dist(x, xi) = ||x - xi||, then ||x - xi|| / rho >= 1, so zeta(x) = 0 by 3(d).

5. zeta is C^1. Fix x in R^m.
 Case x != xi: the Euclidean norm is C^infinity at the nonzero vector x - xi (contDiffAt_norm), so y -> ||y - xi|| / rho is C^infinity at x, and zeta = phi o (y -> ||y - xi|| / rho) is C^1 at x as the composition of the C^1 function phi with a map that is C^1 at x (ContDiff.comp_contDiffAt).
 Case x = xi: the open ball B°_{rho/2}(xi) is a neighbourhood of xi contained in the closed ball B_{rho/2}(xi), on which zeta = 1 by 4(b). So zeta agrees near xi with a constant function and is C^1 at xi (contDiffAt_const.congr_of_eventuallyEq).
 Hence zeta is C^1 at every point, i.e. ContDiff R 1 zeta (contDiff_iff_contDiffAt).

6. Gradient bound. For all x, y in R^m, by 3(b) and the reverse triangle inequality,
 |zeta(x) - zeta(y)| <= 3 | ||x - xi|| - ||y - xi|| | / rho <= (3/rho) ||x - y||.
 So zeta is (3/rho)-Lipschitz on R^m, and a K-Lipschitz map satisfies ||D zeta(x)|| <= K at every point (norm_fderiv_le_of_lipschitz). Hence ||fderiv R zeta x|| <= 3/rho for every x.

7. Steps 4(a), 4(b), 4(c), 5 and 6 are exactly the five asserted properties. (The case m = 0 is included: R^0 is a single point, ||x - xi|| = 0, zeta = phi(0) = 1, and the hypothesis rho <= dist(x, xi) = 0 never holds since rho > 0.) QED

## Key steps

1. Bump g(t) = S(12(t - 1/2)) S(12(1 - t)) with S = Real.smoothTransition: smooth, 0 <= g <= 1, g = 0 for t <= 1/2 and t >= 1, g = 1 on [7/12, 11/12].
2. c = integral_{1/2}^{1} g >= 1/3, so c^{-1} <= 3.
3. phi(t) = 1 - c^{-1} integral_{1/2}^{t} g is C^1 by the FTC, 3-Lipschitz, phi = 1 on (-inf, 1/2], phi = 0 on [1, inf), 0 <= phi <= 1.
4. zeta(x) = phi(||x - xi|| / rho) has values in [0,1], equals 1 on B_{rho/2}(xi) and 0 when dist(x, xi) >= rho.
5. zeta is C^1: the norm is smooth away from xi, and zeta = 1 on a neighbourhood of xi.
6. zeta is (3/rho)-Lipschitz, hence ||fderiv R zeta x|| <= 3/rho for all x.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `timeout 300 rg -n 'aal_l1th|l1_tilt|l1th' <snapshot>/project <snapshot>/mathlib`
- `rg -n 'theorem (dist_starProjection_eq_infDist|norm_sub_starProjection|starProjection_orthogonal|starProjection_orthogonal_val|starProjection_add_starProjection_orthogonal|orthogonalProjection_orthogonal|starProjection_apply_eq_zero_iff|starProjection_apply_mem|trace_starProjection|starProjection_isSymmetric|isSymmetric_starProjection|isIdempotentElem_starProjection|starProjection_idem)' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (trace_smulRight|IsProj.trace|trace_comp_comm|trace_mul_comm|trace_eq_sum_inner|trace_eq_sum_orthonormalBasis|trace_id|trace_one)|lemma (trace_smulRight|IsProj.trace|trace_eq_sum_inner)' <snapshot>/mathlib/Mathlib; rg -n 'starProjection.*trace|trace.*starProjection' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (LocallyIntegrableOn.integrableOn_compact_subset|integrableOn_iff_integrable_of_support_subset|setIntegral_le_integral|Measure.integrableOn_of_bounded|ae_restrict_mem₀|withDensity_absolutelyContinuous|withDensity_apply)|lemma measure_compl_support' <snapshot>/mathlib/Mathlib`
- `rg -n 'integrableOn_of_bounded|comp_aestronglyMeasurable₂' <snapshot>/mathlib/Mathlib; rg -n 'starProjection_norm_le|norm_starProjection_apply_le' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `grep -n '^theorem|^lemma|^protected theorem' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `rg -n 'theorem (integral_hasDerivAt_right|integral_hasStrictDerivAt_right)|theorem norm_fderiv_le_of_lipschitz|theorem contDiff_one_iff_deriv|theorem contDiffAt_norm|theorem contDiff_iff_contDiffAt|theorem integral_mono_on' <snapshot>/mathlib/Mathlib`
- `python3 -I scan of dag.json nodes[*] (lean_name, status) for collisions and sibling-branch statuses; grep -rl aal_l1th .humanize GMT`
- `python3 -I /tmp/l1th-decomp/scripts/gen.py (verifier/lean_contract.py validate_lean_statement + verifier/gmt-compare.py child_modules, contract scope)`
- `lean /tmp/l1th-decomp/children/*/NodeChallenge.lean and NodeSolution.lean against a scratch GMT.Ch05.Submission olean`
- `lean /tmp/l1th-decomp/src/Assembly3.lean (#print axioms aal_l1_tilt_height)`
- `lean /tmp/l1th-decomp/final/All3.lean (#print axioms for the 3 children and the parent)`
- `python3 -I /tmp/l1th-decomp/scripts/numcheck2.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-l1-tilt-height-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-smooth-cutoff-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-projection-algebra-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-height-field-divergence-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/l1th-decomp/src/Assembly3.lean`
- `/tmp/l1th-decomp/final/All3.lean`

**Snapshot and existing names**
- Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- 'aal_l1th|l1_tilt|l1th' has no match in the snapshot project or Mathlib.
- Mathlib has no ready-made lemma for the trace of a starProjection, so the trace identity is a genuine child obligation.

**Mathlib lemmas located** (paths under mathlib/Mathlib)
- Analysis/InnerProductSpace/Projection/Basic.lean:
  - starProjection_orthogonal_val (:203)
  - dist_starProjection_eq_infDist (:234)
  - starProjection_norm_le (:386)
  - norm_starProjection_apply_le (:411)
  - starProjection_isSymmetric (:658)
  - starProjection_apply_eq_zero_iff (:689)
- LinearAlgebra/Trace.lean: trace_mul_comm (:103), trace_comp_comm' (:265), trace_smulRight (:272), IsProj.trace (:327).
- Analysis/InnerProductSpace/Trace.lean: trace_eq_sum_inner (:25). This module is not imported by the contract, but Submission.lean may import it.
- Measure theory:
  - Measure/Support.lean: measure_compl_support (:202)
  - Measure/WithDensity.lean: withDensity_apply (:44), withDensity_absolutelyContinuous (:146)
  - Measure/Restrict.lean: ae_restrict_mem₀ (:637)
  - Function/LocallyIntegrable.lean: LocallyIntegrableOn.integrableOn_compact_subset (:122)
  - Integral/IntegrableOn.lean: integrableOn_iff_integrable_of_support_subset (:462), Measure.integrableOn_of_bounded (:716)
  - Integral/Bochner/Set.lean: setIntegral_congr_fun (:73), integral_indicator (:185), setIntegral_le_integral (:742)
  - Function/StronglyMeasurable/AEStronglyMeasurable.lean: Continuous.comp_aestronglyMeasurable₂ (:263)
- For the cutoff:
  - SmoothTransition.lean: one_of_one_le, zero_of_nonpos, le_one, nonneg, contDiff (:161-205)
  - IntervalIntegral/FundThmCalculus.lean: integral_hasDerivAt_right (:725)
  - ContDiff/Deriv.lean: contDiff_one_iff_deriv (:98)
  - InnerProductSpace/Calculus.lean: contDiffAt_norm (:154)
  - FDeriv/Basic.lean: norm_fderiv_le_of_lipschitz (:947)
  - ContDiff/Defs.lean: contDiff_iff_contDiffAt (:1103)

**Sibling branch**
- The root.tilt_excess_height_estimate-a1 branch has analogous, not yet accepted nodes. Their names are reserved, so unique aal_l1th_* names are used instead.
- Its reviewed constructions (the bump with c >= 1/3, the trace identity, the divergence formula) agree with the natural proofs given here.

**Lean verification**
- The three child types pass validate_lean_statement, and their generated NodeChallenge and NodeSolution modules compile.
- A sorry-free parent assembly compiles from the children plus aal_tangent_structure, whose exact frozen types appear as stubs.
- In the full scratch formalization, the children use only propext, Classical.choice and Quot.sound, and the parent's only remaining sorry is aal_tangent_structure.

**Numerical checks**
- c = 5/12.
- The trace identity, the divergence formula and the absorption inequality all hold.
