# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_pointwise-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.weighted_tangent_pointwise-a1.ball_comparison_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. E := Amb n l, H := muHE[n], f := M.indicator theta (so f = theta on M and f = 0 off M), nu := H restricted to S cap B. This is steps 3-5 of the parent proof at a single scale, with psi in place of phi_r, the measurable set B in place of the ball B_r = closedBall y (r rho), and the constant c in place of theta(y). The hypotheses are: B measurable; M H-null-measurable; theta a.e.-measurable for H restricted to M; H((M cap B) minus S) = 0; H(S cap B) < infinity; psi measurable; |psi w| <= K for all w; psi w = 0 for w not in B; Lambda := lintegral over S cap B of |f w - c|_e dH(w) < infinity. Claim: |integral over M of psi theta dH - c * integral over S of psi dH| <= K * Lambda.toReal.

1. Localizing the S-integral. psi vanishes off B, so setIntegral_eq_integral_of_forall_compl_eq_zero, applied to the measure H restricted to S (no integrability needed), gives integral over S of psi dH = integral of psi d((H restricted to S) restricted to B). Since B is measurable, (H restricted to S) restricted to B = H restricted to (B cap S) (Measure.restrict_restrict). Hence integral over S of psi dH = integral over S cap B of psi dH = integral of psi dnu.

2. Localizing the M-integral. In the same way psi(w) theta(w) = 0 for w not in B, so integral over M of psi theta dH = integral over M cap B of psi theta dH.

3. Replacing M cap B by (S cap B) cap M. We have (M cap B) minus ((S cap B) cap M) = (M cap B) minus S, which is H-null by hypothesis, and ((S cap B) cap M) minus (M cap B) is empty. So M cap B and (S cap B) cap M are H-a.e. equal (ae_eq_set), and integral over M cap B of psi theta dH = integral over (S cap B) cap M of psi theta dH (setIntegral_congr_set; no integrability needed).

4. Inserting the indicator. Pointwise, M.indicator (psi theta)(w) = psi(w) f(w) (Set.indicator_mul_right). M is H-null-measurable and nu <= H, so M is nu-null-measurable. Therefore:
   integral of psi f dnu = integral of M.indicator (psi theta) dnu
   = integral of psi theta d(nu restricted to M) (integral_indicator₀)
   = integral of psi theta d(H restricted to (M cap (S cap B))) (Measure.restrict_restrict₀)
   = integral over (S cap B) cap M of psi theta dH.
   Together with steps 1-3: integral over M of psi theta dH - c * integral over S of psi dH = integral of psi f dnu - c * integral of psi dnu. Steps 1-4 are identities of Bochner integrals and hold without any integrability assumption.

5. Integrability with respect to nu.
   - nu is a finite measure because H(S cap B) < infinity (isFiniteMeasure_restrict).
   - By aemeasurable_indicator_iff₀ (M is H-null-measurable and theta is a.e.-measurable for H restricted to M), f is a.e.-measurable for H. It is therefore a.e.-measurable for nu and, being real-valued, a.e.-strongly measurable for nu; so is f - c.
   - The lintegral of |f - c|_e with respect to nu is Lambda < infinity, so f - c has finite integral and is nu-integrable (hasFiniteIntegral_iff_enorm).
   - Constants are nu-integrable (nu is finite), so f = (f - c) + c is nu-integrable.
   - psi is measurable with |psi| <= K, so it is nu-integrable (Integrable.mono' against the constant K).
   - psi f and psi (f - c) are nu-integrable, being bounded a.e.-strongly measurable functions times integrable ones (Integrable.bdd_mul).

6. Linearity. By step 5:
   integral of psi f dnu - c * integral of psi dnu
   = integral of psi f dnu - integral of c psi dnu (integral_const_mul)
   = integral of (psi f - c psi) dnu (integral_sub)
   = integral of psi (f - c) dnu.

7. Estimate. For every w, |psi(w) (f(w) - c)| = |psi(w)| |f(w) - c| <= K |f(w) - c|, and K |f - c| is nu-integrable by step 5. Hence |integral of psi (f - c) dnu| <= integral of K |f - c| dnu = K * integral of |f - c| dnu (norm_integral_le_of_norm_le, integral_const_mul). Finally, integral of |f - c| dnu = (lintegral of |f - c|_e dnu).toReal = Lambda.toReal (integral_norm_eq_lintegral_enorm; f - c is nu-a.e.-strongly measurable).

8. By steps 4, 6 and 7: |integral over M of psi theta dH - c * integral over S of psi dH| = |integral of psi (f - c) dnu| <= K * Lambda.toReal. QED.

## Key steps

1. psi vanishes off the measurable set B, so the S-integral and the M-integral localize to S cap B and M cap B
2. H((M cap B) minus S) = 0 makes M cap B a.e. equal to (S cap B) cap M, and integral_indicator₀ turns the M-integral into the integral over S cap B of psi * 1_M theta
3. finite H(S cap B), a.e.-measurability of 1_M theta and the finite lintegral make 1_M theta - c, 1_M theta, psi and the products integrable on S cap B
4. linearity gives the difference as the integral over S cap B of psi (1_M theta - c)
5. |psi| <= K and integral_norm_eq_lintegral_enorm bound it by K times the toReal of the lintegral

## Reference use

### local-project

Queries:
- `cat <run>/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-weighte-2b8750410f/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `grep -n 'def |theorem ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 1,130p; sed -n 210,366p (blowUpMap l.96, HasApproximateTangentSpaceAt l.102, HasWeightedApproximateTangentSpaceAt l.330)`
- `python3 -I scan of dag.json: children of root.density_one_higher_regularity-a1.graph_tangent_planes-a1; nodes whose lean_name/lean_statement mention blowUp; status/candidate_commit/proof_base_commit/title/statement of rsod_blowUp_setIntegral_eq`
- `git show 98fd790d5bc2f705d0efa953dadfb274b5462997:GMT/Ch05/Submission.lean; git log --oneline -6 98fd790d; git diff --stat ea56075 98fd790d`
- `cat nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ch-45b63ae1fc/{isolated-comparator-result.json,lean-audit-v1.json,comparator-v1.log,parent-supplied-natural-proof.md}`
- `sed -n 4300,4420p; sed -n 6480,6620p; sed -n 3140,3215p; sed -n 1640,1680p; sed -n 1815,1850p; grep -n 'def _accepted_checkpoint' -A 30 /runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/runtime.py`
- `grep -n 'max_nodes|max_children|max_depth' /runtime/flows/gmt-claude-6e6a457c9391/__init__.py; cat swarm-project.json`
- `sed -n 1,110p; sed -n 419,470p; sed -n 545,645p verifier/gmt-compare.py; grep -n 'def validate_lean_statement' -A 60 _recursive_lean/lean_contract.py; sed -n 1,80p _recursive_lean/decomposition_scope.py`
- `rg -n 'theorem (setIntegral_eq_integral_of_forall_compl_eq_zero|setIntegral_congr_set|integral_indicator₀|setIntegral_indicator|norm_integral_le_of_norm_le|integral_norm_eq_lintegral_enorm|integral_smul_measure|integral_const_mul)\b' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (restrict_restrict|restrict_restrict₀|aemeasurable_indicator_iff₀|hasFiniteIntegral_iff_enorm)\b' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem Integrable.bdd_mul|theorem tendsto_toReal|^theorem toReal_mul |theorem ae_eq_set|MeasurableEmbedding.integral_map|euclideanHausdorffMeasure_homothety_image|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_smul₀' <snapshot>/mathlib/Mathlib`
- `rg -n 'dohr_tp_wtlp|wtlp|ball_comparison_le|rescaled_limit' <snapshot>; grep -c dohr_tp_wtlp dag.json; grep -rl dohr_tp_wtlp <run>/nodes GMT .lake/packages/simongmt`
- `diff -q <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; diff GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `lean -o build/GMT/Ch05/Submission.olean src/Submission.lean (fresh scratch compile of the frozen Submission)`
- `lean src/Probe.lean (#check of the cited Mathlib/SimonGMT lemmas under import GMT.Ch05.Submission)`
- `python3 -I /tmp/wtp-scripts/gen_children.py children.json gen (lean_contract.validate_lean_statement + gmt-compare.child_modules contract mode)`
- `lean src/Assembly.lean (frozen parent type from the three children stated with sorry)`
- `lean src/ChildB.lean; lean src/ChildC.lean (complete proofs of the two new children)`
- `lean -o full/GMT/Ch05/Submission.olean fullsrc/Submission.lean (accepted proof of child 1 + children 2, 3 + parent); lean src/Axioms.lean (#print axioms); lean gen/NodeChallenge_*.lean gen/NodeSolution_*.lean against that build`
- `python3 -I /tmp/wtp-scripts/build_final.py (validator, key/name uniqueness, identical-type check against dag.json)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-weighte-2b8750410f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-weighte-2b8750410f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-weighte-2b8750410f/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ch-45b63ae1fc/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ch-45b63ae1fc/lean-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ch-45b63ae1fc/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ch-45b63ae1fc/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/swarm-project.json`
- `/runtime/flows/gmt-claude-6e6a457c9391/__init__.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/decomposition_scope.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/wtp-split-urTIc4/src/Probe.lean`
- `/tmp/wtp-split-urTIc4/src/Assembly.lean`
- `/tmp/wtp-split-urTIc4/src/ChildB.lean`
- `/tmp/wtp-split-urTIc4/src/ChildC.lean`
- `/tmp/wtp-split-urTIc4/src/Axioms.lean`
- `/tmp/wtp-split-urTIc4/fullsrc/Submission.lean`
- `/tmp/wtp-split-urTIc4/gen/NodeChallenge_ball_comparison_bound.lean`
- `/tmp/wtp-split-urTIc4/gen/NodeSolution_ball_comparison_bound.lean`
- `/tmp/wtp-scripts/gen_children.py`
- `/tmp/wtp-scripts/children.json`
- `/tmp/wtp-scripts/build_final.py`

Snapshot and workspace agree:
- The snapshot pins project ea56075 and Mathlib 25730c7c.
- The snapshot's GMT/Ch05/Submission.lean is byte-identical to the workspace copy, which matches Contract.lean.
- SimonGMT Chapter03/Rectifiable.lean defines blowUpMap (l.96), HasApproximateTangentSpaceAt (l.102) and HasWeightedApproximateTangentSpaceAt (l.330), which the frozen types use.

The DAG already holds Submission.rsod_blowUp_setIntegral_eq:
- Node root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_change_of_variables-a1, status accepted, candidate commit 98fd790d.
- Its isolated comparator passed ('Your solution is okay!') and its machine-leaf lean audit passed.
- Its frozen type is string-identical to step 1 of this proof specialized to g(y) = f(y) theta(x + r y).
- runtime.py allows reusing accepted checkpoints with an identical frozen type and overlays them into the parent worktree.

The pinned Mathlib supplies every lemma the child proofs cite:
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486)
- setIntegral_congr_set (:77)
- integral_indicator₀ (:170)
- Measure.restrict_restrict / restrict_restrict₀ (Measure/Restrict.lean:205/198)
- aemeasurable_indicator_iff₀ (AEMeasurable.lean:323)
- hasFiniteIntegral_iff_enorm (HasFiniteIntegral.lean:90)
- Integrable.bdd_mul (Integrable.lean:1067)
- integral_norm_eq_lintegral_enorm (Bochner/Basic.lean:537)
- norm_integral_le_of_norm_le (:985)
- integral_smul_measure (:1052)
- MeasurableEmbedding.integral_map (:1093)
- integral_const_mul (:290)
- ae_eq_set (OuterMeasure/AE.lean:231)
- ENNReal.tendsto_toReal (ENNReal/Lemmas.lean:102)
- ENNReal.toReal_mul (Basic/ENNReal/Real.lean:337)
- Isometry.euclideanHausdorffMeasure_image, Measure.euclideanHausdorffMeasure_smul₀, euclideanHausdorffMeasure_homothety_image (Volume/Measure.lean:131/152/164)

No existing declaration covers the fixed-scale comparison or the rescaled limit. rg finds no 'dohr_tp_wtlp' or 'wtlp' in the snapshot, dag.json, node directories, GMT or simongmt, so both new names are free.

Lean checks, against a fresh scratch build of the frozen Submission:
- All three child statements pass validate_lean_statement and elaborate in the verifier-generated NodeChallenge modules.
- The exact frozen parent type is proved from the three children (Assembly.lean).
- Children 2 and 3 have complete proofs.
- A combined build with the accepted proof of child 1 reports #print axioms = [propext, Classical.choice, Quot.sound] for all three children and the parent, and every NodeSolution `exact Submission.X` closes.
