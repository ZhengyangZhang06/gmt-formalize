# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.lusin_exhaustion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof: Lusin's theorem, Simon Ch. 1, Theorem 1.17, used as in Simon Ch. 3, Remark 1.8(1).

The parent invokes SimonGMT's Chapter01.IsBorelRegularOuterMeasure.exists_isClosed_continuousOn. However, the module Poincare.SimonGMT.Chapter01.Lusin is not in the import closure of GMT.Ch05.Submission: after `import GMT.Ch05.Submission`, `#check` reports that constant, and Chapter01.exists_isClosed_continuousOn_of_measurable, as unknown. The proof below therefore proves Lusin's theorem directly for the finite Borel measure ν := Hⁿ⌞A. Closed inner regularity of finite Borel measures on a metric space replaces Simon's Theorem 1.15, and a countable family of rational intervals is used. No new import is used. The same argument is already formalized in this project for the accepted declaration Submission.aetp_lusin_compact_exhaustion (commit 2bf50ebc).

Notation: Hⁿ := μHE[n]; ν := Hⁿ⌞A (Measure.restrict); for q = (a, b) ∈ ℚ × ℚ, I_q := (a, b) ⊆ ℝ.

1. Regularity of ν. ν is finite, since ν(ℝ^{n+ℓ}) = Hⁿ(A) < ∞ (isFiniteMeasure_restrict). A finite Borel measure on a pseudometrizable space is weakly regular (Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure). Hence for every Borel set S and every δ ∈ [0, ∞] with δ ≠ 0 there is a closed F ⊆ S with ν(S ∖ F) < δ (MeasurableSet.exists_isClosed_sdiff_lt, using ν(S) ≠ ∞).

2. Lusin for ν. Claim: for every ε ∈ [0, ∞] with ε ≠ 0 there is a closed C ⊆ A with ν(A ∖ C) < ε and ϑ continuous on C.
(a) Choice of weights. ℚ × ℚ is countable, so there are δ_q ∈ ℝ≥0 with δ_q > 0 and ∑_q δ_q < ε (ENNReal.exists_pos_sum_of_countable).
(b) Inner approximation for one interval. Fix q. The sets P_q := A ∩ ϑ⁻¹(I_q) and N_q := A ∖ ϑ⁻¹(I_q) are Borel, because A is Borel, ϑ is measurable and I_q is open. By step 1 there are closed F_q ⊆ P_q and F'_q ⊆ N_q with ν(P_q ∖ F_q) < δ_q/2 and ν(N_q ∖ F'_q) < δ_q/2 (note δ_q/2 ≠ 0). A point z ∈ A ∖ (F_q ∪ F'_q) lies in P_q ∖ F_q if ϑ(z) ∈ I_q, and in N_q ∖ F'_q otherwise. Hence ν(A ∖ (F_q ∪ F'_q)) ≤ δ_q/2 + δ_q/2 = δ_q (measure_union_le).
(c) The set C. Put C := ⋂_q (F_q ∪ F'_q).
- C is closed, being an intersection of closed sets.
- For q₀ := (0, 0), C ⊆ F_{q₀} ∪ F'_{q₀} ⊆ P_{q₀} ∪ N_{q₀} ⊆ A.
- A ∖ C = ⋃_q (A ∖ (F_q ∪ F'_q)). So ν(A ∖ C) ≤ ∑_q ν(A ∖ (F_q ∪ F'_q)) ≤ ∑_q δ_q < ε (measure_iUnion_le, ENNReal.tsum_le_tsum).
(d) ϑ is continuous on C. Let z ∈ C and e > 0. Choose rationals a, b with ϑ(z) − e < a < ϑ(z) < b < ϑ(z) + e (exists_rat_btwn), and put q := (a, b).
- Since ϑ(z) ∈ I_q, z ∉ N_q, hence z ∉ F'_q.
- F'_q is closed, so its complement is open and there is s > 0 with B̆_s(z) ∩ F'_q = ∅.
- Let y ∈ C with dist(y, z) < s. Then y ∈ F_q ∪ F'_q and y ∉ F'_q, so y ∈ F_q ⊆ P_q, i.e. a < ϑ(y) < b.
- Hence |ϑ(y) − ϑ(z)| < e. This is continuity of ϑ on C (Metric.continuousOn_iff).

3. The sets C_m. For m ∈ ℕ apply step 2 with ε := (m : [0, ∞])⁻¹. This is ≠ 0 because (m : [0, ∞]) ≠ ∞ (ENNReal.inv_ne_zero, ENNReal.natCast_ne_top). It gives a closed C_m ⊆ A with ϑ continuous on C_m and ν(A ∖ C_m) < m⁻¹. Since A ∖ C_m is Borel and contained in A, ν(A ∖ C_m) = Hⁿ((A ∖ C_m) ∩ A) = Hⁿ(A ∖ C_m) (Measure.restrict_apply). Hence Hⁿ(A ∖ C_m) < m⁻¹ for every m; for m = 0 the bound is 0⁻¹ = ∞.

4. Conclusion. By step 3 the sequence (C_m)_{m∈ℕ} satisfies the first conjunct. For the second, suppose h := Hⁿ(A ∖ ⋃_i C_i) ≠ 0. Then there is m ∈ ℕ with m⁻¹ < h (ENNReal.exists_inv_nat_lt). Since A ∖ ⋃_i C_i ⊆ A ∖ C_m, monotonicity and step 3 give h ≤ Hⁿ(A ∖ C_m) < m⁻¹ < h, a contradiction. Hence Hⁿ(A ∖ ⋃_i C_i) = 0. ∎

## Key steps

1. ν := Hⁿ⌞A is a finite, hence weakly regular, Borel measure, so every Borel set contains a closed set of almost full ν-measure
2. for each rational interval q: closed F_q ⊆ A ∩ ϑ⁻¹(q) and F'_q ⊆ A ∖ ϑ⁻¹(q) with ν(A ∖ (F_q ∪ F'_q)) ≤ δ_q, where ∑ δ_q < ε
3. C := ⋂_q (F_q ∪ F'_q) is closed, C ⊆ A and ν(A ∖ C) < ε; ϑ is continuous on C because points of C near z avoid the closed set F'_q
4. taking ε = 1/m gives closed C_m ⊆ A with ϑ continuous on C_m and Hⁿ(A ∖ C_m) < 1/m
5. Hⁿ(A ∖ ⋃ C_m) < 1/m for every m, hence it is 0

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
