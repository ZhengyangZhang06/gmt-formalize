# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.varifold_graph_transfer-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.varifold_graph_transfer-a1.transfer_consequences-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This child is steps 5 and 6 of the proof of gwe_varifold_graph_transfer, stated for an abstract Borel map G. The parent applies it with mu = V.weight, S = q '' graphOver f A, G = Fh (the Borel version of the graph map) and its density W. No extra import is needed.

Notation. L^n := volume on R^n, and nu := (L^n restricted to A).withDensity (ofReal o W), a measure on R^n. For a set T, 1_T := T.indicator 1.

1. Pushforward identity (step 6a): mu restricted to S = Measure.map G nu. By Measure.ext it suffices to check that both measures agree on every Borel set T of R^{n+l}.
 - Left side. T is Borel, so (mu restricted to S)(T) = int 1_T d(mu restricted to S) = int_S 1_T dmu (lintegral_indicator_one). The function 1_T is Borel, so the hypothesis gives (mu restricted to S)(T) = int_A ofReal(W(x)) 1_T(G(x)) dx.
 - Right side. G is Borel, so G^{-1}(T) is Borel. Then (Measure.map G nu)(T) = nu(G^{-1}(T)) (Measure.map_apply) = int_{G^{-1}(T)} ofReal(W) d(L^n restricted to A) (withDensity_apply) = int (G^{-1}(T)).indicator(ofReal o W) d(L^n restricted to A) (lintegral_indicator).
 - Pointwise, (G^{-1}(T)).indicator(ofReal o W)(x) = ofReal(W(x)) 1_T(G(x)): both equal ofReal(W(x)) if G(x) is in T, and 0 otherwise. So the two values coincide (lintegral_congr).
2. Proof of (i) (step 6b). Let phi : R^{n+l} -> R be Borel. Then:
 int_S phi dmu = int phi d(Measure.map G nu), by step 1;
 = int phi(G(x)) dnu(x), by integral_map (G is measurable, hence a.e. measurable for nu; phi is Borel, hence a.e. strongly measurable for Measure.map G nu);
 = int_A (ofReal(W(x))).toReal phi(G(x)) dx, by integral_withDensity_eq_integral_toReal_smul (ofReal o W is Borel and ofReal(W(x)) < infinity for every x);
 = int_A W(x) phi(G(x)) dx, since toReal(ofReal(W(x))) = W(x) for W(x) >= 0 and the scalar action is multiplication.
 Neither integral_map nor integral_withDensity_eq_integral_toReal_smul assumes integrability. Each is an identity of Bochner integrals in Lean's convention: if one side is not integrable, neither is the other, and both are 0. So (i) holds for every Borel phi.
3. Proof of (ii) (step 5). Let mu(Z) = 0 and choose a Borel set Z' containing Z with mu(Z') = 0 (exists_measurable_superset_of_null). The function 1_{Z'} is Borel, so the hypothesis and lintegral_indicator_one give
 int_A ofReal(W(x)) 1_{Z'}(G(x)) dx = int_S 1_{Z'} dmu = (mu restricted to S)(Z') <= mu(Z') = 0 (Measure.restrict_apply_le).
4. The integrand x |-> ofReal(W(x)) 1_{Z'}(G(x)) is Borel, since W, G and Z' are Borel. By lintegral_eq_zero_iff it vanishes (L^n restricted to A)-a.e. As A is Borel, this means (ae_restrict_iff'): for L^n-a.e. x, if x is in A then ofReal(W(x)) 1_{Z'}(G(x)) = 0.
5. Take such an x with x in A and G(x) in Z. Since Z ⊆ Z', 1_{Z'}(G(x)) = 1, so ofReal(W(x)) = 0, i.e. W(x) <= 0 (ENNReal.ofReal_eq_zero). With W(x) >= 0 this gives W(x) = 0. This proves (ii). QED

## Key steps

1. Pushforward identity mu|S = Measure.map G ((L^n|A).withDensity(ofReal o W)), checked on Borel T with phi = 1_T (lintegral_indicator_one, Measure.map_apply, withDensity_apply, lintegral_indicator).
2. integral_map and integral_withDensity_eq_integral_toReal_smul, with toReal(ofReal W) = W, give (i) for every Borel phi without integrability assumptions.
3. For mu-null Z take a Borel mu-null Z' containing Z; the hypothesis with phi = 1_{Z'} gives int_A ofReal(W) 1_{Z'}(G) dL^n <= mu(Z') = 0.
4. lintegral_eq_zero_iff and ae_restrict_iff' give ofReal(W x) 1_{Z'}(G x) = 0 for a.e. x in A, hence W x = 0 whenever G x is in Z.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean (both identical); cat <snapshot>/manifest.json; lake env printenv LEAN_PATH`
- `python3 -I: dag.json census (431 nodes, 431 unique lean_names; gwe_* names and statuses; JB and AREA lean_statements; parent lean_statement == handoff == prompt type)`
- `grep -c gwe_vgt dag.json (0); grep -rl gwe_vgt nodes (no match); grep -rn gwe_vgt GMT (no match); grep -rln 'gwe_vgt|weight_density|transfer_consequences|graph_measurability' <snapshot>/project/GMT (no match)`
- `python3 -I: dag.json accepted nodes anyrad_gc_graph_lintegral_transfer, anyrad_gc_volume_le_graph_hausdorff, anyrad_gc_hausdorff_restrict_le_weight, anyrad_gc_graph_tangentProj_ae, lip_approx_graph_measure, dohr_lmo_weight_restrict_eq, dohr_lmo_hausdorff_null_of_weight_null (statement, lean_statement)`
- `python3 -I: dag.json cross-branch dependency census and children of split nodes with external depends_on`
- `grep -rli varifold --include=*.lean <snapshot>/mathlib/Mathlib (0 files)`
- `grep -rn 'theorem ContinuousOn.measurable_piecewise|theorem MeasurableSet.image_of_continuousOn_injOn|theorem lintegral_withDensity_eq_lintegral_mul_non_measurable₀|theorem integral_withDensity_eq_integral_toReal_smul |theorem restrict_withDensity |theorem aemeasurable_indicator_iff₀|theorem lintegral_indicator₀|theorem exists_measurable_superset_of_null|theorem measurable_fderiv |theorem Continuous.matrix_det|def finAddEquivProd|theorem setLIntegral_congr_fun_ae|theorem setLIntegral_congr_fun |theorem setIntegral_congr_fun |theorem integral_map |theorem restrict_restrict₀ |theorem restrict_restrict |theorem lintegral_eq_zero_iff |theorem lintegral_indicator_one |theorem withDensity_apply |theorem map_apply ' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem setLIntegral_one|theorem ae_restrict_iff' |protected theorem continuousOn|theorem restrict_apply_le|theorem restrict_le_self|theorem NullMeasurableSet.mono' <snapshot>/mathlib/Mathlib; grep -n 'theorem continuous_matrix|continuous_toLp|continuous_apply|toLp_apply' Topology/Instances/Matrix.lean Analysis/Normed/Lp/PiLp.lean; sed -n 360,384p Analysis/InnerProductSpace/PiL2.lean; sed -n 350,395p Analysis/Calculus/FDeriv/Measurable.lean`
- `sed -n 520,640p verifier/gmt-compare.py; python3 -I scripts/scope.py (contract_scope); python3 -I scripts/gen_challenges.py (child_modules, mode contract)`
- `grep -n 'area formula|4.5 Theorem' book/chapter-05.txt; sed -n 880,912p book/chapter-05.txt`
- `lean -o /tmp/vgt-decomp-20261012/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (contract-only)`
- `lean checks/challenge/gwe_vgt_{weight_density,graph_measurability,transfer_consequences}_challenge.lean`
- `lean checks/Assembly.lean (#print axioms parent_check); lean checks/C1.lean, C2.lean, C3.lean (#print axioms c1_check, c2_check, c3_check); lean checks/Inst.lean`
- `lean -o olean2/GMT/Ch05/Submission.olean sub2/GMT/Ch05/Submission.lean (contract + three child theorems); lean checks/challenge/*_solution.lean; lean checks/Axioms2.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-varifold-graph-transfer-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-varifold-graph-transfer-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-varifold-graph-transfer-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-lipschitz-graph-area-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/vgt-decomp-20261012/checks/Defs.lean`
- `/tmp/vgt-decomp-20261012/checks/Assembly.lean`
- `/tmp/vgt-decomp-20261012/checks/C1.lean`
- `/tmp/vgt-decomp-20261012/checks/C2.lean`
- `/tmp/vgt-decomp-20261012/checks/C3.lean`
- `/tmp/vgt-decomp-20261012/checks/Inst.lean`
- `/tmp/vgt-decomp-20261012/checks/Axioms2.lean`
- `/tmp/vgt-decomp-20261012/checks/challenge/gwe_vgt_weight_density_challenge.lean`
- `/tmp/vgt-decomp-20261012/checks/challenge/gwe_vgt_graph_measurability_challenge.lean`
- `/tmp/vgt-decomp-20261012/checks/challenge/gwe_vgt_transfer_consequences_challenge.lean`
- `/tmp/vgt-decomp-20261012/sub2/GMT/Ch05/Submission.lean`

Revisions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. lake env resolves Mathlib and simongmt 2b36630 from lake-packages-25730c7c.

Contract definitions used:
- RectifiableVarifold fields nullMeasurableSet_carrier, mult_pos and aemeasurable_mult.
- weight = ((muHE[n]).restrict carrier).withDensity (ofReal o mult).
- graphPoint x y = toLp 2 (Fin.append (ofLp x) (ofLp y)).
- graphOver f D = (x |-> graphPoint x (f x)) '' D.

Names and dependencies.
- No gwe_vgt_ name occurs in dag.json (431 unique names), in nodes/**, in the workspace GMT sources or in the snapshot project. The three new names are free.
- gwe_graph_jacobian_bounds and gwe_lipschitz_graph_area_formula are still 'decomposing', so no child may depend on them; the glue that uses them stays in the parent.

Reuse candidates inspected and not reused: anyrad_gc_volume_le_graph_hausdorff, anyrad_gc_graph_lintegral_transfer, anyrad_gc_hausdorff_restrict_le_weight, lip_approx_graph_measure, dohr_lmo_weight_restrict_eq, dohr_lmo_hausdorff_null_of_weight_null. None has a child's type, and the supplied proof gets (P5) and (P6) from AREA and JB.

No-match: Mathlib has no varifold file (0 matches), so the weight-density child is proved from the contract definitions.

Mathlib items located in the snapshot:
- WithDensity.lean: withDensity_apply (44), restrict_withDensity (215), lintegral_withDensity_eq_lintegral_mul_non_measurable₀ (508).
- Bochner: integral_withDensity_eq_integral_toReal_smul (ContinuousLinearMap.lean:318), integral_map (Basic.lean:1081), setIntegral_congr_fun (Set.lean:73).
- ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean:523); MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821).
- measurable_fderiv (FDeriv/Measurable.lean:378).
- Topology/Instances/Matrix.lean: continuous_matrix (97), Continuous.matrix_det (212).
- PiLp.lean: toLp_apply (141), continuous_apply and continuous_toLp (540-547). EuclideanSpace.finAddEquivProd (PiL2.lean:378).
- aemeasurable_indicator_iff₀ (AEMeasurable.lean:323).
- Lebesgue/Basic.lean: setLIntegral_one (124), setLIntegral_congr_fun_ae (290), setLIntegral_congr_fun (298), lintegral_eq_zero_iff (349), lintegral_indicator₀ (518), lintegral_indicator_one (572).
- Restrict.lean: restrict_le_self (141), restrict_apply_le (176), restrict_restrict₀ (198), restrict_restrict (205), ae_restrict_iff' (629).
- NullMeasurableSet.mono (Filter.lean:66); exists_measurable_superset_of_null (MeasureSpaceDef.lean:219); Measure.map_apply (Map.lean:170); LipschitzOnWith.continuousOn (EMetricSpace/Lipschitz.lean:308).

Source. Simon Ch. 5, proof of Theorem 4.5 (book lines 747 and 896-912) is the context of the transfer step.

Lean results:
- All three verifier-generated challenges elaborate.
- parent_check derives the exact frozen parent type from JB, AREA and the three children.
- c1_check, c2_check and c3_check prove the three children.
- The NodeSolution files elaborate against a Submission containing the three theorems.
- Every check uses only propext, Classical.choice and Quot.sound.
