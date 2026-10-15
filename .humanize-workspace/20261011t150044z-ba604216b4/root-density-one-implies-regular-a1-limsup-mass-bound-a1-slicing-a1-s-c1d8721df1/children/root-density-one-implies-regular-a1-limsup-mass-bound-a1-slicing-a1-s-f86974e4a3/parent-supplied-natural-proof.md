# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.tangential_gradient-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.tangential_gradient-a1.weak_limit_gluing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Step 7, which dominates the piece integrals, sums over the pieces P_j and applies dominated convergence for series. This is Simon's reduction to one piece in the proof of Ch. 6, Lemma 4.5(2): M = ⋃_j M_j disjoint with Hⁿ(M_0) = 0, and "we have merely to check that (1) holds with N_j in place of M_j and with v vanishing on ℝ^{n+ℓ} ∖ M_j" (chapter-06.txt ll. 1246–1262).

All integrals are Bochner integrals with respect to μ.

[Import: tendsto_tsum_of_dominated_convergence lives in Mathlib.Analysis.Normed.Group.Tannery. GMT.Ch07.Submission does not import it transitively (checked with #check), so add `import Mathlib.Analysis.Normed.Group.Tannery`. Alternatively, use the self-contained argument written out in step 6.]

Notation: a_j(k) := ∫_{S_j} u_k dμ, a_j := ∫_{S_j ∩ E} v dμ, β_j := ∫_{S_j} D dμ.

1. Null modification.
 - ⋃_j S_j ⊆ M and μ(M ∖ ⋃_j S_j) = 0, so M and ⋃_j S_j coincide μ-a.e. Hence μ⌞M = μ⌞(⋃_j S_j) (Measure.restrict_congr_set).
 - (⋃_j S_j) ∩ E = ⋃_j (S_j ∩ E) differs from M ∩ E by a subset of M ∖ ⋃_j S_j, which is null. Hence μ⌞(M ∩ E) = μ⌞(⋃_j (S_j ∩ E)).

2. Integrability.
 - Fix k. u_k is μ⌞M-a.e. strongly measurable, |u_k| ≤ D μ⌞M-a.e., and D is integrable on M. So u_k is integrable on M (Integrable.mono'), hence on ⋃_j S_j by step 1.
 - D is integrable on ⋃_j S_j and on each S_j, because these sets lie in M.
 - v is integrable on M ∩ E, hence on ⋃_j (S_j ∩ E) by step 1.

3. Series for the sequence. The S_j are Borel and pairwise disjoint, and u_k is integrable on their union (step 2). Countable additivity of the Bochner integral (integral_iUnion) and step 1 give, for every k,
 ∫_M u_k dμ = ∫_{⋃_j S_j} u_k dμ = Σ_j a_j(k).

4. Series for the limit. The sets S_j ∩ E are Borel (E is Borel) and pairwise disjoint, and v is integrable on their union (step 2). So
 ∫_{M∩E} v dμ = ∫_{⋃_j (S_j∩E)} v dμ = Σ_j a_j.

5. Domination.
 - Fix k and j. Since S_j ⊆ M, |u_k| ≤ D holds μ⌞S_j-a.e., and D is integrable on S_j. So |a_j(k)| ≤ ∫_{S_j} D dμ = β_j (norm_integral_le_of_norm_le).
 - The S_j are Borel and pairwise disjoint and D is integrable on their union, so (β_j) has sum ∫_{⋃_j S_j} D dμ (hasSum_integral_iUnion). In particular Σ_j β_j converges.

6. Tannery's theorem (dominated convergence for series; Mathlib tendsto_tsum_of_dominated_convergence). By hypothesis a_j(k) → a_j as k → ∞ for each j. Also |a_j(k)| ≤ β_j for all k and j, and Σ_j β_j < ∞. Hence Σ_j a_j(k) → Σ_j a_j as k → ∞.
 Self-contained argument:
 - Letting k → ∞ in |a_j(k)| ≤ β_j gives |a_j| ≤ β_j, so both series converge absolutely.
 - Given ε > 0, choose N with Σ_{j>N} β_j < ε/3. Then
 |Σ_j a_j(k) − Σ_j a_j| ≤ Σ_{j≤N} |a_j(k) − a_j| + Σ_{j>N} (|a_j(k)| + |a_j|) ≤ Σ_{j≤N} |a_j(k) − a_j| + 2ε/3.
 - The finite sum Σ_{j≤N} |a_j(k) − a_j| tends to 0 as k → ∞, so it is < ε/3 for all large k.

7. Conclusion. By steps 3 and 4, the convergence in step 6 is exactly ∫_M u_k dμ → ∫_{M∩E} v dμ as k → ∞. ∎

## Key steps

1. M =ᵐ ⋃_j S_j and M ∩ E =ᵐ ⋃_j (S_j ∩ E), so the restricted measures agree (Measure.restrict_congr_set).
2. u_k is integrable on M by domination (Integrable.mono'); D is integrable on each S_j; v is integrable on ⋃_j (S_j ∩ E).
3. Countable additivity (integral_iUnion) gives ∫_M u_k = Σ_j a_j(k) and ∫_{M∩E} v = Σ_j a_j.
4. |a_j(k)| ≤ β_j := ∫_{S_j} D, and (β_j) is summable with sum ∫_{⋃ S_j} D (hasSum_integral_iUnion).
5. Tannery's theorem (tendsto_tsum_of_dominated_convergence, or the ε/3 argument) gives Σ_j a_j(k) → Σ_j a_j, which is the claim.

## Reference use

### local-project

Queries:
- `python3 -I: read nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/decomposition-v1.json (frozen lean_statement of chart_pieces, piece_coarea, piece_slice_tangent, piece_weak_limit, tangential_gradient) and assert equality with the selected node's parent-child-handoff.json lean_statement`
- `grep -rn 'theorem HasApproximateTangentSpaceAt.unique\|countablyRectifiable_iUnion\|def HasApproximateTangentSpaceAt\|def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/`
- `grep -rn 'theorem MeasurableSet.image_of_continuousOn_injOn\|theorem lintegral_iUnion\|theorem AEMeasurable.ennreal_tsum\|theorem lintegral_tsum\|theorem setLIntegral_eq_of_support_subset\|theorem integral_iUnion\|theorem hasSum_integral_iUnion\|theorem tendsto_tsum_of_dominated_convergence\|theorem ae_restrict_iUnion_iff' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn 'theorem setLIntegral_mono\|theorem integrable_toReal_of_lintegral_ne_top\|comp_aestronglyMeasurable₂\|theorem integrable_indicator_iff\|theorem Measurable.inner\|measurable_from_nat' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `#check probes after `import GMT.Ch07.Submission`: tendsto_tsum_of_dominated_convergence (unknown identifier), MeasureTheory.integral_iUnion, MeasureTheory.lintegral_tsum, AEMeasurable.ennreal_tsum, MeasureTheory.setLIntegral_eq_of_support_subset, MeasureTheory.ae_restrict_iUnion_iff, MeasurableSet.image_of_continuousOn_injOn`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `dag.json lean_name collision scan for dor_lmbsf_tg_coarea_gluing, dor_lmbsf_tg_tangent_gluing, dor_lmbsf_tg_weak_limit_gluing; regex 'tendsto_tsum_of_dominated|Tannery|glu(e|ing)|countable (disjoint )?union of (the )?pieces|dominated convergence for series' over node statements and titles`
- `grep -rl dor_lmbsf_tg_ nodes/ dag.json; git log --all --oneline -S dor_lmbsf_tg_`
- `grep -n '1.3 Remark\|1.5 Remarks\|2.1 Definition\|We now conclude 2.4 by summing\|This follows from the C 1 case\|2.10 Remarks' book/chapter-03.txt; grep -n '4.1 Lemma\|Furthermore for any non-negative\|To prove (2) we ﬁrst recall\|we have merely to check' book/chapter-06.txt`
- `python3 -I verifier lean_contract.validate_lean_statement + gmt-compare.contract_scope(Contract.lean, 'GMT.Ch07.main_theorem'); lake env lean /tmp/tg-decomp/Elab.lean; lake env lean /tmp/tg-decomp/Assembly.lean (#print axioms TGTest.assembly); lake env lean /tmp/tg-decomp/ChildProofs.lean (#print axioms of the three child proofs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-c1d8721df1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-c1d8721df1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-c1d8721df1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/tg-decomp/Elab.lean`
- `/tmp/tg-decomp/Assembly.lean`
- `/tmp/tg-decomp/ChildProofs.lean`

Snapshot: project b4d606d, mathlib 25730c7c; simongmt 2b36630 comes from the lake-packages tree. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No existing declaration or DAG node states the three gluing lemmas, so all three names are fresh.

Library facts used by the children (snapshot mathlib):
- lintegral_iUnion and setLIntegral_eq_of_support_subset (Integral/Lebesgue/Basic.lean:597, 545);
- lintegral_tsum (Lebesgue/Add.lean:362);
- AEMeasurable.ennreal_tsum (BorelSpace/Real.lean:378, a deprecated alias of AEMeasurable.tsum);
- integral_iUnion and hasSum_integral_iUnion (Bochner/Set.lean:324, 331);
- ae_restrict_iUnion_iff (Measure/Restrict.lean:565);
- tendsto_tsum_of_dominated_convergence (Analysis/Normed/Group/Tannery.lean:45). It is not reachable from `import GMT.Ch07.Submission` (#check gives unknown identifier), so weak_limit_gluing needs `import Mathlib.Analysis.Normed.Group.Tannery`.

Library facts used by the parent assembly:
- MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821; Lusin–Souslin, for P_j Borel);
- SimonGMT HasApproximateTangentSpaceAt.unique (Rectifiable.lean:232) and countablyRectifiable_iUnion (Rectifiable.lean:76);
- integrable_toReal_of_lintegral_ne_top, integrable_indicator_iff and Continuous.comp_aestronglyMeasurable₂.
- Measurable.inner is unavailable; continuous_inner.comp_aestronglyMeasurable₂ replaces it.

Book anchors:
- Ch. 3: Remark 1.3 (ll. 67–72), Remark 1.5 (ll. 86–90), 2.1 (ll. 337–350), the proof of 2.4 by summing over j (ll. 378–395), and 2.8–2.9 (ll. 412–435);
- Ch. 6: Lemma 4.1 (ll. 1156–1183) and the one-piece reduction in the proof of 4.5(2) (ll. 1246–1262).

Lean checks:
- Elab.lean: all three child types elaborate in the comparator scope.
- Assembly.lean: proves the exact frozen parent type from the 4 sibling types and the 3 child types; axioms propext, Classical.choice, Quot.sound.
- ChildProofs.lean: all 3 children proved; same axioms.
