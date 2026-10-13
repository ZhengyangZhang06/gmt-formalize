# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.freeze_weight-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9 of the parent proof: J₁(r) − ϑ(x)∫_{η(C_i)} f → 0, by continuity of ϑ on C_i and the bounded density ratio of step 6. It is stated on the original side of the blow-up. The bounded density ratio is a hypothesis here; in the parent it is supplied by the sibling ball_mass_bound.

Notation: Hⁿ := μHE[n]; η_r := blowUpMap x r; B_ρ(p) := closedBall p ρ; E(r) := (rⁿ)⁻¹·∫_C f(η_r(z))(ϑ(z) − ϑ(x)) dHⁿ(z). Fix f ∈ C_c(ℝ^{n+ℓ}, ℝ).

1. Bounds for f. As f is continuous with compact support, there is M with |f(y)| ≤ M for all y (Continuous.bounded_above_of_compact_support); M ≥ |f(0)| ≥ 0. As tsupport f is compact, hence bounded, tsupport f ⊆ B_{R₀}(0) for some R₀. Put R := max(R₀, 1) > 0. Then f(y) = 0 whenever y ∉ B_R(0) (image_eq_zero_of_notMem_tsupport).

2. Localization. If r > 0 and z ∉ B_{rR}(x), then ‖z − x‖ > rR, so ‖η_r(z)‖ = r⁻¹‖z − x‖ > R and f(η_r(z)) = 0 by step 1.

3. Density bound. Apply the hypothesis with this R > 0: there are Λ ∈ ℝ and a set U₁ ∈ 𝓝[>] 0 such that (rⁿ)⁻¹·Hⁿ.real(C ∩ B_{rR}(x)) ≤ Λ for r ∈ U₁. Put Λ' := max(Λ, 0) ≥ 0. The measure Hⁿ⌞C is finite since Hⁿ(C) < ∞ (isFiniteMeasure_restrict).

4. Choice of δ and r. Let ε > 0; we show |E(r)| < ε eventually in 𝓝[>] 0 (Metric.tendsto_nhds).
- Put ε' := ε/((M + 1)(Λ' + 1)) > 0.
- By ContinuousWithinAt ϑ C x (Metric.continuousWithinAt_iff) there is δ > 0 such that |ϑ(z) − ϑ(x)| < ε' for all z ∈ C with dist(z, x) < δ.
- The interval (0, δ/R) belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT).
- Fix r ∈ U₁ ∩ (0, δ/R). Then r > 0 and rR < δ. Let B := B_{rR}(x), a Borel set.

5. Pointwise bound on C. For every z ∈ C: |f(η_r(z))·(ϑ(z) − ϑ(x))| ≤ 1_B(z)·Mε'.
- If z ∈ B, then dist(z, x) ≤ rR < δ, so |ϑ(z) − ϑ(x)| < ε'. Also |f(η_r(z))| ≤ M; multiply, using M ≥ 0.
- If z ∉ B, the left side is 0 by step 2.

6. Integral bound. As C is Borel, step 5 holds Hⁿ⌞C-a.e. (ae_restrict_of_forall_mem). The function 1_B·Mε' is Hⁿ⌞C-integrable: it is a constant times the indicator of a Borel set, for a finite measure. By norm_integral_le_of_norm_le (no integrability of the integrand is needed):
|∫_C f(η_r(z))(ϑ(z) − ϑ(x)) dHⁿ(z)| ≤ ∫_C 1_B·Mε' dHⁿ = Mε'·Hⁿ.real(C ∩ B) (integral_indicator, setIntegral_const, Measure.restrict_apply with B Borel).

7. Estimate of E(r). Using step 3 (r ∈ U₁, Mε' ≥ 0):
|E(r)| = (rⁿ)⁻¹·|∫_C …| ≤ Mε'·((rⁿ)⁻¹·Hⁿ.real(C ∩ B)) ≤ Mε'·Λ' = ε·MΛ'/((M + 1)(Λ' + 1)) < ε.
The last step holds because 0 ≤ MΛ' < (M + 1)(Λ' + 1).

8. Conclusion. For every ε > 0, |E(r)| < ε for all r in U₁ ∩ (0, δ/R) ∈ 𝓝[>] 0. Hence E(r) → 0 as r ↓ 0. ∎

## Key steps

1. |f| ≤ M and f = 0 off B_R(0); hence f(η_r z) = 0 off B_{rR}(x)
2. bounded density ratio: (rⁿ)⁻¹Hⁿ(C ∩ B_{rR}(x)) ≤ Λ' = max(Λ, 0) eventually
3. continuity of ϑ within C at x: |ϑ(z) − ϑ(x)| < ε' on C ∩ B_{rR}(x) once rR < δ
4. |E(r)| ≤ Mε'(rⁿ)⁻¹Hⁿ(C ∩ B_{rR}(x)) ≤ Mε'Λ' < ε

## Reference use

### local-project

Queries:
- `cat parent-child-handoff.json, parent-supplied-plan.md and parent-supplied-natural-proof.json of node root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-298de173be`
- `python3 over dag.json: status, lean_name and lean_statement of all nodes under root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- `python3 over dag.json: nodes whose lean_name or lean_statement mentions blowUp, Lusin, withDensity or continuousOn; duplicate lean_name check; exact string comparison of the selected, rsod_blowUp_setIntegral_eq and rsod_ae_tendsto_density_zero_outside types`
- `grep -n 'def blowUpMap|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `#check of 31 cited library names after `import GMT.Ch05.Submission` (Scratch/LibCheck.lean), including Chapter01.IsBorelRegularOuterMeasure.exists_isClosed_continuousOn, Chapter01.exists_isClosed_continuousOn_of_measurable and Chapter01.closedSetsAreGDelta_iff`
- `grep -rln Lusin <snapshot>/mathlib/Mathlib/MeasureTheory`
- `git show 98fd790d (rsod_blowUp_setIntegral_eq) and 2bf50ebc (aetp_lusin_compact_exhaustion); git branch -a --contains 98fd790d; git merge-base --is-ancestor 98fd790d on every ae-approx-tangent branch; git diff --stat ea560759 4426c5c3/e85cf00b/98fd790d -- GMT/`
- `grep -n '_existing_lean_name_problem|_overlay_accepted_children|_accepted_checkpoint|def _solve_children|def ensure' /runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/{runtime,store}.py`
- `grep -rl rsod_wfu over the run dir (excluding local-references), GMT, .lake/packages/simongmt, <snapshot>/project and <snapshot>/mathlib/Mathlib; git grep -q rsod_wfu <tip> -- '*.lean' over 402 distinct ref tips`
- `grep -n '1.5 Remark|1.8 Remark|1.17 Theorem' book/chapter-03.txt and book/chapter-01.txt`
- `grep import/prefix/frozen in verifier/gmt-compare.py and verifier/lean_contract.py`
- `cmp GMT/Ch05/{Submission,Contract}.lean against the snapshot project copies; lake-manifest.json revisions`
- `lake build GMT.Ch05.Submission and lake env lean Scratch/{Stmts,Assembly,Pointwise,LibCheck,Tail,Freeze,Mass,Lusin,All2,Challenge2,Solution2}.lean in /tmp/wfu-decomp-Y9uffV`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-298de173be/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-298de173be/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ch-45b63ae1fc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ch-45b63ae1fc/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/store.py`
- `/tmp/wfu-decomp-Y9uffV/Scratch/LibCheck.lean`
- `/tmp/wfu-decomp-Y9uffV/Scratch/All2.lean`
- `/tmp/wfu-decomp-Y9uffV/Scratch/Challenge2.lean`
- `/tmp/wfu-decomp-Y9uffV/Scratch/Solution2.lean`
- `/tmp/wfu-decomp-Y9uffV/Scratch/final_stmts.json`

Pins and frozen definitions:
- Project ea560759 (workspace HEAD, equal to the manifest project_commit), Mathlib 25730c7c, simongmt 2b366308.
- The workspace Submission.lean and Contract.lean are byte-identical to the snapshot copies.
- The selected node's dispatch base 4426c5c3 adds no Lean declarations.
- Rectifiable.lean confirms the frozen definitions: blowUpMap x r y = r⁻¹ • (y − x), and both approximate-tangent predicates are finrank P = n plus the 𝓝[>] 0 limit for every f : C_c.

Lusin:
- SimonGMT's Chapter01 Lusin theorems (IsBorelRegularOuterMeasure.exists_isClosed_continuousOn, exists_isClosed_continuousOn_of_measurable) and closedSetsAreGDelta_iff are unknown after `import GMT.Ch05.Submission`.
- In snapshot Mathlib/MeasureTheory, 'Lusin' occurs only in Jacobian.lean and Constructions/Polish/Basic.lean (Lusin–Souslin), not as a Lusin continuity theorem.
- So the Lusin child uses Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure, MeasurableSet.exists_isClosed_sdiff_lt and rational intervals, as accepted commit 2bf50ebc does for aetp_lusin_compact_exhaustion.
- The 31 cited names were checked by #check after `import GMT.Ch05.Submission`: 26 resolve (integral_inter_add_sdiff, norm_integral_le_of_norm_le, Integrable.bdd_mul, withDensity_apply, Measure.restrict_restrict, …). Of the 5 that fail, 4 are the unreachable SimonGMT names above and Lusin's IsCaratheodoryMeasurable-based route that the proofs do not use. The fifth, MeasureTheory.MeasurableEmbedding.integral_map, simply lives in the root namespace as MeasurableEmbedding.integral_map, which the accepted cov proof uses. Every other cited name is exercised by the compiled scratch proofs.

Reuse:
- rsod_blowUp_setIntegral_eq is accepted (node root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_change_of_variables-a1, candidate 98fd790d, which adds only that theorem). Its dag.json type is string-identical to the proposed blowup_cov type.
- The controller (runtime.py _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children; store.ensure) shares such accepted nodes across branches.
- The accepted aetp_lusin_compact_exhaustion, tae_mult_lusin_compact_pieces and aetp_weightedTangent_of_lusin_compact require a RectifiableVarifold (countably rectifiable carrier, positive multiplicity), so they do not apply to a general A and real-valued ϑ.

Names: the prefix rsod_wfu occurs nowhere in:
- dag.json or other run files (local-references excluded);
- GMT, simongmt, the snapshot project or snapshot Mathlib;
- .lean files at any of the 402 distinct git ref tips.

Source text: book/chapter-03.txt (Remarks 1.5(3), 1.8(1); Def. 1.7) and book/chapter-01.txt (Thm 1.17) match the children.

Lean (scratch /tmp/wfu-decomp-Y9uffV, v4.35.0-rc3):
- All 7 types elaborate in the frozen Contract scope, and every `exact Submission.X` typechecks.
- The five new children (with the accepted cov proof) have complete proofs whose axioms are only propext, Classical.choice and Quot.sound.
- The selected theorem compiles from them, with sorryAx only from the stubbed dependency rsod_ae_tendsto_density_zero_outside.
- The scratch Submission.lean was restored to pristine afterwards.

No Matrix/IsUnit construction occurs.
