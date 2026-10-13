# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_rate-a1.height_transfer-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_rate-a1.height_transfer-a1.pointwise_height-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. N := n + l, so Amb n l = R^N. For a in R^n and c in R^l, graphPoint(a, c) = toLp(Fin.append a c): its coordinate at Fin.castAdd l i is a_i (i < n), and its coordinate at Fin.natAdd n j is c_j (j < l). Every index of Fin N has exactly one of these two forms (Fin.addCases). |.| is the Euclidean norm and ||A|| the operator norm. q is linear with |q z| = |z|, and P is linear. Real division by 0 gives 0.
The two coordinate identities (G1), (G4) are proved below from the definition of graphPoint; the projection properties are exactly the hypotheses (H1), (H2).

1. (G1) For all a, a' in R^n and c, c' in R^l: graphPoint(a + a', c + c') = graphPoint(a, c) + graphPoint(a', c'). Compare coordinates: at castAdd l i both sides equal a_i + a'_i, and at natAdd n j both equal c_j + c'_j.

2. (G4) For all a in R^n and c in R^l: |graphPoint(a, c)|^2 = |a|^2 + |c|^2. In each Euclidean space |z|^2 = sum_k |z_k|^2 = sum_k z_k^2 (EuclideanSpace.norm_sq_eq; for real coordinates |z_k|^2 = z_k^2). Split the sum over Fin (n + l) into its castAdd and natAdd parts (Fin.sum_univ_add): sum_i a_i^2 + sum_j c_j^2 = |a|^2 + |c|^2.

3. Let Y := q(graphPoint(x, b)) and RHS := 2^(n+4) (|Y - P Y|^2 / |Y|^(n+2)). We have 2^(n+4) > 0, |Y - P Y|^2 >= 0 and |Y|^(n+2) >= 0. A nonnegative real divided by a nonnegative real is >= 0 (it is 0 if the denominator is 0). So RHS >= 0.

4. Case x = 0. Then |x|^(n+2) = 0^(n+2) = 0 because n + 2 >= 1. So the left side is |b - A x|^2 / 0 = 0 <= RHS by step 3.

5. Case x != 0, so |x| > 0. Put w := b - A x, T := q(graphPoint(x, A x)) and y_w := q(graphPoint(0, w)).
(a) Decomposition. Since x + 0 = x and A x + w = b, (G1) gives graphPoint(x, b) = graphPoint(x, A x) + graphPoint(0, w). Applying the linear map q: Y = T + y_w.
(b) Residual. By linearity of P and (H1), P Y = P T + P y_w = T + P y_w. Hence Y - P Y = y_w - P y_w.
(c) Normal bound. Since 0 <= ||A|| <= 1/7, we have 1 + ||A||^2 <= 1 + 1/49 <= 4 = 2^2, so (1 + ||A||^2)^(1/2) <= 2 (Real.sqrt_le_left). By (H2) for this w and by (b):
|w| <= (1 + ||A||^2)^(1/2) |y_w - P y_w| <= 2 |y_w - P y_w| = 2 |Y - P Y|.
Both sides are >= 0, so squaring gives |w|^2 <= (2 |Y - P Y|)^2 = 4 |Y - P Y|^2.
(d) Size of Y. q is an isometry, so |Y| = |graphPoint(x, b)|, and by (G4) |Y|^2 = |x|^2 + |b|^2.
- Since |b|^2 >= 0, |x|^2 <= |Y|^2. As |x| >= 0 and |Y| >= 0, this gives |x| <= |Y| (sq_le_sq₀). In particular |Y| > 0.
- Since 0 <= |b| <= |x|/7, |b|^2 <= |x|^2/49. So |Y|^2 <= (50/49)|x|^2 <= 4|x|^2 = (2|x|)^2. As |Y| >= 0 and 2|x| >= 0, this gives |Y| <= 2|x|.
(e) Powers. Let k := n + 2. From 0 <= |Y| <= 2|x|: |Y|^k <= (2|x|)^k = 2^k |x|^k (pow_le_pow_left₀, mul_pow). Also |x|^k > 0 and |Y|^k > 0.
(f) Combination. Since |x|^k > 0, the claim |w|^2 / |x|^k <= RHS is equivalent to |w|^2 <= RHS * |x|^k (div_le_iff₀). The chain below uses (c), then |Y|^k > 0, then (e) together with 4|Y - P Y|^2 / |Y|^k >= 0, and finally 4 * 2^k = 2^(n+4):
|w|^2 <= 4|Y - P Y|^2 = (4|Y - P Y|^2 / |Y|^k) |Y|^k <= (4|Y - P Y|^2 / |Y|^k)(2^k |x|^k) = 2^(n+4) (|Y - P Y|^2 / |Y|^k) |x|^k = RHS * |x|^k.
Since w = b - A x, this is the claim.

6. Steps 4 and 5 cover every x. This proves the statement for all n, l, q, P, A, x and b satisfying the hypotheses.

## Key steps

1. Coordinate identities: (G1) additivity of graphPoint and (G4) |graphPoint(a, c)|^2 = |a|^2 + |c|^2
2. x = 0: |x|^(n+2) = 0, so the left side is 0 <= RHS
3. x != 0: Y = q(graphPoint(x, A x)) + q(graphPoint(0, w)) with w = b - A x, and (H1) gives Y - P Y = y_w - P y_w
4. (H2) with (1 + ||A||^2)^(1/2) <= 2 gives |w|^2 <= 4 |Y - P Y|^2
5. |Y|^2 = |x|^2 + |b|^2 and |b| <= |x|/7 give |x| <= |Y| <= 2|x|, hence |Y|^(n+2) <= 2^(n+2) |x|^(n+2)
6. Combine: |w|^2 / |x|^(n+2) <= 2^(n+4) |Y - P Y|^2 / |Y|^(n+2)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean and Submission.lean against the workspace copies; git -C lake-packages-25730c7c/mathlib rev-parse HEAD; git -C <snapshot>/mathlib rev-parse HEAD; cmp of the 13 cited Mathlib files between <snapshot>/mathlib and lake-packages-25730c7c/mathlib`
- `python3 -I dump of dag.json graph_rate children (lean_name, lean_statement, depends_on) and of nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-v2.json, nodes/root-allard-any-radius-a1-graph-rate-a1-plane-projections-a1/decomposition-v1.json and decomposition-audit-v1.json, and this node's parent-child-handoff.json`
- `rg -n "theorem lintegral_const_mul'|theorem lintegral_mono_set|theorem lintegral_eq_zero_iff'|theorem measure_toMeasurable|theorem subset_toMeasurable|theorem measurableSet_toMeasurable|theorem lintegral_indicator_one|theorem norm_image_sub_le_of_norm_fderiv_le|theorem ContinuousOn.aemeasurable|theorem ae_eq_mk|theorem measurable_mk|theorem lintegral_congr_ae|theorem lintegral_mono_ae|theorem ae_restrict_mem|theorem ofReal_mul|theorem EuclideanSpace.norm_sq_eq" <snapshot>/mathlib/Mathlib`
- `rg -n "clm_apply|apply_continuousLinearMap" <snapshot>/mathlib/Mathlib/MeasureTheory; rg -n "Continuous.clm_apply|ContinuousOn.prodMk|continuous_of_finiteDimensional|AEMeasurable.ennreal_ofReal|ContDiffOn.differentiableOn" <snapshot>/mathlib/Mathlib`
- `rg -n "sqrt_le_left|sqrt_le_iff|le_sqrt" Mathlib/Analysis/Real/Sqrt.lean; rg -n "pow_le_pow_left₀|pow_le_pow_iff_left₀|sq_le_sq₀|div_le_iff₀" Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `grep -l any_radius_gr_ht_ dag.json nodes/*/*.json <snapshot>/project; python3 -I scan of all 555 lean_name fields; git grep -l -e any_radius_gr_ht_ -- '*.lean' over 683 distinct git ref tips`
- `python3 -I comparison of both child lean_statements with every DAG lean_statement; dump of anyrad_gc_graph_lintegral_transfer and gwe_varifold_graph_transfer`
- `lake build GMT.Ch05.Submission in /tmp/ht-decomp-m71UOw/proj (copy of the pinned snapshot project, .lake/packages linked to lake-packages-25730c7c)`
- `lake env lean Checks/Types.lean (child, parent, la_basics and plane_projections types in the comparator scope)`
- `lake env lean Checks/Proofs.lean (complete proofs of both child types and of the parent type from the child and prerequisite types; #print axioms)`
- `gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement to generate NodeSolution files; lake build of a scratch Submission containing the child declarations; lake env lean Checks/NodeSolution_{ae_transfer,pointwise_height,parent}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-height-transfer-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-height-transfer-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-plane-projections-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-plane-projections-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ht-decomp-m71UOw/proj/Checks/Types.lean`
- `/tmp/ht-decomp-m71UOw/proj/Checks/Proofs.lean`
- `/tmp/ht-decomp-m71UOw/proj/Checks/NodeSolution_ae_transfer.lean`
- `/tmp/ht-decomp-m71UOw/proj/Checks/NodeSolution_pointwise_height.lean`
- `/tmp/ht-decomp-m71UOw/proj/Checks/NodeSolution_parent.lean`
- `/tmp/ht-decomp-m71UOw/proj/GMT/Ch05/Submission.lean`

Snapshot
- The snapshot is pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- Its Contract.lean and Submission.lean are byte-identical to the workspace copies.
- The 13 cited Mathlib files are byte-identical to the compiler package at the same revision.

Mathlib facts behind the split
- ae_transfer uses:
  - AEMeasurable.mk, measurable_mk, ae_eq_mk (MeasureSpaceDef.lean:439-442);
  - toMeasurable, subset_toMeasurable, measurableSet_toMeasurable, measure_toMeasurable (MeasureSpaceDef.lean:333-348);
  - lintegral_indicator_one (Lebesgue/Basic.lean:572), lintegral_eq_zero_iff' (:322), lintegral_congr_ae (:275).
  - None of these needs sigma-finiteness or measurability of the original integrand.
- pointwise_height uses EuclideanSpace.norm_sq_eq (PiL2.lean:149), Real.sqrt_le_left (Sqrt.lean:223), and pow_le_pow_left₀, sq_le_sq₀, div_le_iff₀ (GroupWithZero/Basic.lean:513, 758, 1132).
- The parent assembly uses:
  - lintegral_const_mul' (Lebesgue/Add.lean:420), which needs no measurability;
  - lintegral_mono_set (Lebesgue/Basic.lean:98), lintegral_mono_ae (:217);
  - ContinuousOn.aemeasurable (IntegrableOn.lean:754);
  - Convex.norm_image_sub_le_of_norm_fderiv_le (MeanValue.lean:499), ContDiffOn.differentiableOn with n != 0 (ContDiff/Defs.lean:578);
  - Continuous.clm_apply (BoundedLinearMaps.lean:471), AEMeasurable.ennreal_ofReal (BorelSpace/Real.lean:188), ae_restrict_mem (Restrict.lean:640).
- There is no AEStronglyMeasurable.clm_apply, so evaluation is handled by Continuous.clm_apply composed with AEStronglyMeasurable.prodMk. Also, AEStronglyMeasurable.div does not apply to real division, so the AEMeasurable route is used.

No-match results
- any_radius_gr_ht_ occurs in no dag.json or nodes/*/*.json lean_name, no snapshot project file, and no .lean file on 683 distinct git ref tips.
- No DAG lean_statement equals either child type.

Lean
- Both child types, the parent type and the two prerequisite types elaborate in the comparator scope.
- Both children are proved in full from the frozen contract.
- The exact parent type is proved from the child types plus the la_basics and plane_projections types.
- Axioms: only propext, Classical.choice and Quot.sound.
- Comparator-style NodeSolution checks pass by exact Submission.X. The parent target's only sorryAx comes from the simulated prerequisite stand-ins.
