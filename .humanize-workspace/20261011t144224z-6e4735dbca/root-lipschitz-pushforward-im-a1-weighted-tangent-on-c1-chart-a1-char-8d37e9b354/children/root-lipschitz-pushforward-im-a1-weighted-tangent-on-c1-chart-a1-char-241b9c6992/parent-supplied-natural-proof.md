# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_area_formula-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_area_formula-a1.signed_of_lintegral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Setting and notation.
- Φ : ℝⁿ → ℝ^Q is continuous; Ω, s ⊆ ℝⁿ are open with s ⊆ Ω and s bounded; Φ is injective on Ω.
- J : ℝⁿ → ℝ is continuous with J ≥ 0.
- h : ℝ^Q → ℝ is continuous with compact support; K := tsupport h; Ω ∩ Φ⁻¹(K) ⊆ s.
- (H): for every Borel g : ℝ^Q → [0, ∞], ∫⁻_{Φ(s)} g dHⁿ = ∫⁻_s ofReal(J(v))·g(Φ(v)) dLⁿ(v).
- Hⁿ = μHE[n] on ℝ^Q and Lⁿ = volume on ℝⁿ; ∫ is the Bochner set integral, ∫⁻ the lintegral. Write F(v) := J(v)·h(Φ(v)).
- This is steps 5–6 of the parent proof, together with the Borel measurability of Φ(Ω) from step 2(b). (H) is the identity the parent obtains in step 4, with J = JΦ.
- Hⁿ(Φ(s)) < ∞ is obtained from (H) with g ≡ 1 instead of the Lipschitz image bound of parent step 3. This is the same finiteness the parent uses in step 5.

1. (Vanishing off K.) If y ∉ K, then h(y) = 0 (`image_eq_zero_of_notMem_tsupport`).

2. (Bounds.)
   (a) s is bounded in the proper space ℝⁿ, so its closure is compact (`Bornology.IsBounded.isCompact_closure`). J is continuous, so there is J_max with |J(v)| ≤ J_max on the closure of s (`IsCompact.exists_bound_of_continuousOn`). Since J ≥ 0, we get 0 ≤ J(v) ≤ J_max for every v ∈ s.
   (b) h is continuous with compact support, so there is M with |h(y)| ≤ M for all y (`Continuous.bounded_above_of_compact_support`).
   (c) Lⁿ(s) < ∞, because s is bounded and Lⁿ is finite on compact sets (`Bornology.IsBounded.measure_lt_top`).

3. (Hⁿ(Φ(s)) < ∞.) Apply (H) to the measurable function g ≡ 1. Then Hⁿ(Φ(s)) = ∫⁻_{Φ(s)} 1 dHⁿ = ∫⁻_s ofReal(J(v))·1 dLⁿ. Since ofReal is monotone and J ≤ J_max on s, this is ≤ ∫⁻_s ofReal(J_max) dLⁿ = ofReal(J_max)·Lⁿ(s), which is < ∞ by 2(c).

4. (Integrability.)
   - h is continuous (hence strongly measurable), |h| ≤ M, and Hⁿ(Φ(s)) < ∞ by step 3. So h is Hⁿ-integrable on Φ(s) (`Measure.integrableOn_of_bounded`).
   - F is continuous, since J, h and Φ are, hence strongly measurable. For v ∈ s, |F(v)| = J(v)|h(Φ(v))| ≤ J_max·M by 2(a) and 2(b). Since Lⁿ(s) < ∞, F is Lⁿ-integrable on s.

5. (The two nonnegative identities.) The functions g₊ := ofReal ∘ h and g₋ := ofReal ∘ (−h) are Borel, because h is continuous and ofReal is measurable. By (H):
   ∫⁻_{Φ(s)} ofReal(h) dHⁿ = ∫⁻_s ofReal(J(v))·ofReal(h(Φ(v))) dLⁿ, and
   ∫⁻_{Φ(s)} ofReal(−h) dHⁿ = ∫⁻_s ofReal(J(v))·ofReal(−h(Φ(v))) dLⁿ.
   Since J(v) ≥ 0 and ofReal(a)·ofReal(b) = ofReal(ab) for a ≥ 0 (`ENNReal.ofReal_mul`), the right-hand integrands are ofReal(F(v)) and ofReal(J(v)·(−h(Φ(v)))) = ofReal(−F(v)).

6. (Signed identity on s.) For an integrable real function f, ∫ f = toReal(∫⁻ ofReal(f)) − toReal(∫⁻ ofReal(−f)) (`integral_eq_lintegral_pos_part_sub_lintegral_neg_part`). Apply this to h on (Φ(s), Hⁿ) and to F on (s, Lⁿ); both are integrable by step 4. Substituting the two identities of step 5 gives
   ∫_{Φ(s)} h dHⁿ = toReal(∫⁻_s ofReal(F) dLⁿ) − toReal(∫⁻_s ofReal(−F) dLⁿ) = ∫_s F dLⁿ.

7. (Measurability of Φ(Ω).) Ω is open, hence Borel. Φ is continuous on Ω and injective on Ω, and ℝⁿ is Polish. By the Lusin–Souslin theorem (`MeasurableSet.image_of_continuousOn_injOn`), Φ(Ω) is Borel.

8. (Extension on the source.) Let v ∈ Ω ∖ s. Then Φ(v) ∉ K, since otherwise v ∈ Ω ∩ Φ⁻¹(K) ⊆ s. By step 1, h(Φ(v)) = 0, so F(v) = 0. Since s ⊆ Ω and Ω is measurable, ∫_Ω F dLⁿ = ∫_s F dLⁿ (`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`).

9. (Extension on the target.) Let y ∈ Φ(Ω) ∖ Φ(s) and write y = Φ(v) with v ∈ Ω. Then v ∉ s (otherwise y ∈ Φ(s)), so Φ(v) ∉ K as in step 8, and h(y) = 0. Since Φ(s) ⊆ Φ(Ω) and Φ(Ω) is measurable by step 7, the same lemma gives ∫_{Φ(Ω)} h dHⁿ = ∫_{Φ(s)} h dHⁿ.

10. (Conclusion.) By steps 9, 6 and 8: ∫_{Φ(Ω)} h dHⁿ = ∫_{Φ(s)} h dHⁿ = ∫_s F dLⁿ = ∫_Ω J(v)h(Φ(v)) dLⁿ(v). ∎

Lean note: every lemma used is in the frozen scope `import GMT.Ch06.Submission`. The proof is a single theorem with no imports and no helpers.

## Key steps

1. h vanishes off K = tsupport h. Bounds: 0 ≤ J ≤ J_max on s (compact closure), |h| ≤ M, Lⁿ(s) < ∞ (s bounded).
2. (H) with g ≡ 1 gives Hⁿ(Φ(s)) ≤ ofReal(J_max)·Lⁿ(s) < ∞. Hence h is integrable on (Φ(s), Hⁿ) and J·(h∘Φ) is integrable on (s, Lⁿ).
3. (H) with g = ofReal∘h and g = ofReal∘(−h), together with J ≥ 0 and ENNReal.ofReal_mul, gives the positive- and negative-part identities. integral_eq_lintegral_pos_part_sub_lintegral_neg_part then yields ∫_{Φ(s)} h dHⁿ = ∫_s J·(h∘Φ) dLⁿ.
4. Φ(Ω) is Borel (Lusin–Souslin). The integrands vanish on Ω∖s and on Φ(Ω)∖Φ(s), so setIntegral_eq_of_subset_of_forall_sdiff_eq_zero extends the identity to Ω and Φ(Ω).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n in snapshot mathlib/Mathlib for: 'theorem normDet_sq_eq_det_gram' | 'theorem normDet_nonneg' | 'theorem MeasurableSet.image_of_continuousOn_injOn' | 'lipschitzOnWith_of_nnnorm_fderiv_le' | 'theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part' | 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero' | 'lemma Measure.integrableOn_of_bounded' | 'bounded_above_of_compact_support' | 'theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume' | 'theorem finrank_euclideanSpace_fin' | 'theorem fderivWithin_of_isOpen' | 'basisFun_apply' | 'def gram'`
- `grep -rn 'IsBounded.measure_lt_top|isCompact_closure|lipschitzOnWith_empty' in mathlib Typeclasses/Finite.lean, MetricSpace/Bounded.lean, EMetricSpace/Lipschitz.lean`
- `rg -n --glob '*.lean' in snapshot project for: 'chart_area_formula' | 'areaJacobianWithin|weighted_area_formula|normDet' | 'lpf_wtc' | 'HasCompactSupport'`
- `cmp snapshot mathlib files (NormDet, Polish/Basic, MeanValue, Bochner/Set, Bochner/Basic, Euclidean/Volume/Measure, PiL2) and project Contract.lean against the pinned lake-packages-25730c7c / workspace copies; git rev-parse HEAD of mathlib and simongmt packages`
- `sed -n 1,200p simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean; rg -n 'def weightedAreaFiberSum|def areaFiber|def areaJacobianAt|areaJacobianAt_eq_normDet' Poincare/SimonGMT/; sed -n 1,80p Chapter02/AreaMultiplicity.lean and Chapter02/Area.lean`
- `Lean scope test (exact comparator prefix from gmt-compare contract_scope): env.contains for LinearMap.normDet, Matrix.gram, Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitzOn_fiberSum, areaJacobianWithin (all false) and MeasurableSet.image_of_continuousOn_injOn, Convex.lipschitzOnWith_of_nnnorm_fderiv_le, Continuous.matrix_det, fderivWithin_of_isOpen, MeasureTheory.integral_map (true)`
- `python3 listing of dag.json (226 nodes; lean_name collision check; children of the selected node); grep of rlcr-plan-v1.md of the accepted leaf chart_image_measurable_finite for the leaf import/helper rule; scan of all 6e4735dbca branches for Submission import changes; grep of nodes/*/decomposition-v*.json rationales for leaf import gates (local_lipschitz_area, slice_mass_bound, pushforward_integrality)`
- `lake build GMT.Ch06.Submission and lake env lean on /tmp/caf_scratch_WCGRI4/Scratch/{ChildA,Full,C1,C2,NodeSolution_P,NodeSolution_C1,NodeSolution_C2,NodeChallenge_*}.lean; gmt-compare child_modules(contract mode) and lean_contract.validate_lean_statement on the child statements`
- `grep -n '3.2|3.5|area formula' book/chapter-02.txt; sed -n 740,800p (Simon Ch. 2 §3, (3.1)-(3.5))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/run.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8d37e9b354/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-1f4173ea67/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-1f4173ea67/lean-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-local-li-2809c506b6/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/76bc108496c244659ad30448cab757f3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/caf_scratch_WCGRI4/Scratch/C1.lean`
- `/tmp/caf_scratch_WCGRI4/Scratch/C2.lean`
- `/tmp/caf_scratch_WCGRI4/Scratch/Full.lean`
- `/tmp/caf_scratch_WCGRI4/Scratch/NodeSolution_P.lean`
- `/tmp/caf_scratch_WCGRI4/Scratch/NodeSolution_C1.lean`
- `/tmp/caf_scratch_WCGRI4/Scratch/NodeSolution_C2.lean`
- `/tmp/caf_scratch_WCGRI4/GMT/Ch06/Submission.lean`
- `/tmp/caf_tools/parent_body.lean`

Snapshot and pins:
- The snapshot pins project d8d46c95 and Mathlib 25730c7c.
- The cited snapshot Mathlib files are byte-identical to lake-packages-25730c7c.
- SimonGMT is at 2b36630.
- The snapshot project contains no chart area formula, normDet or lpf_wtc declaration (rg found no match for those queries).

What the supplied proof needs, and where it lives:
- Step 1: Mathlib NormDet.lean:303 `normDet_sq_eq_det_gram` and :75 `normDet_nonneg`; GramMatrix.lean:39 `Matrix.gram` = `of fun i j ↦ ⟪v i, v j⟫`; PiL2.lean:806 `basisFun_apply`.
- Step 4: SimonGMT Chapter02/AreaDomain.lean `weighted_area_formula_lipschitzOn_fiberSum`, `areaJacobianWithin` = normDet of `fderivWithin`.
- None of these is in the frozen comparator scope (`env.contains` false). They arrive with `import Poincare.SimonGMT.Chapter02.AreaDomain`.

Gates:
- Machine leaves may not change imports or add helpers (leaf rlcr plan).
- Non-leaf nodes have added imports, e.g. weighted_tangent_ae via AreaBranches.
- Hence the import-dependent steps 1 and 4 stay in this parent, and the import-free steps 2–3 and 5–6 become the two children.

Import-free lemmas used by the children, all in scope:
- `MeasurableSet.image_of_continuousOn_injOn` (Polish/Basic.lean:821);
- `Convex.lipschitzOnWith_of_nnnorm_fderiv_le` (MeanValue.lean:507);
- `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` (Bochner/Basic.lean:486);
- `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero` (Bochner/Set.lean:466);
- `Measure.integrableOn_of_bounded` (IntegrableOn.lean:716);
- `Continuous.bounded_above_of_compact_support` (Normed/Group/Bounded.lean:153);
- `Bornology.IsBounded.measure_lt_top` (Typeclasses/Finite.lean:357) and `.isCompact_closure` (MetricSpace/Bounded.lean:328);
- `lipschitzOnWith_empty`;
- `fderivWithin_of_isOpen` (FDeriv/Basic.lean:525).

Verification:
- Both child statements pass lean_contract and compile in the exact comparator scope as single import-free theorems with standard axioms.
- The parent assembly compiles with only the AreaDomain import added; the parent and child NodeSolution files close with [propext, Classical.choice, Quot.sound].
- Simon Ch. 2 (3.2), (3.3), (3.5) (book/chapter-02.txt lines 743–797) confirm Jf = √det(DᵢfDⱼf) and the weighted fibre-sum area formula used in step 4.
