# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.tangent_locality-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.tangent_locality-a1.tangent_growth-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent-supplied proof, i.e. Simon Ch. 3, Remark 1.5(3) (chapter-03.txt lines 91–95). Testing Definition 1.4 with a cutoff that equals 1 on B_1(0) bounds the density ratio.
Notation: E := Euclid P = ℝ^P, H^n := μHE[n], η_ρ := blowUpMap x ρ (so η_ρ(z) = ρ⁻¹(z − x)). Integrals are Bochner integrals.
We use the sibling lemma blowup_scaling: for ρ > 0, R ∈ ℝ and any S ⊆ E,
 H^n(η_ρ(S) ∩ B̄_R(0)) = ((ENNReal.ofReal ρ)⁻¹)^n · H^n(S ∩ B̄_{ρR}(x)).
1. Test function. Let φ(w) := max(0, min(1, 2 − ‖w‖)).
- φ is continuous.
- If ‖w‖ > 2 then 2 − ‖w‖ < 0, so φ(w) = 0. Hence φ vanishes outside the compact ball B̄_2(0), and φ is an element of C_c(E, ℝ) (HasCompactSupport.intro with isCompact_closedBall).
- 0 ≤ φ ≤ 1 everywhere, and φ(w) = 1 when ‖w‖ ≤ 1 (then 2 − ‖w‖ ≥ 1).
2. Choice of C and r₁. Let Λ := ∫_Q φ dH^n ∈ ℝ and C := |Λ| + 1.
- The second component of the tangent hypothesis, with f := φ, gives I(ρ) := ∫_{η_ρ(D)} φ dH^n → Λ as ρ → 0 in 𝓝[>] 0.
- Since Λ ≤ |Λ| < C, eventually I(ρ) < C (Tendsto.eventually_lt_const).
- Also eventually ρ < r₀/2, because (0, r₀/2) ∈ 𝓝[>] 0.
- The conjunction holds eventually in 𝓝[>] 0. By mem_nhdsGT_iff_exists_Ioo_subset there is r₁ > 0 such that every ρ ∈ (0, r₁) satisfies I(ρ) < C and ρ < r₀/2.
3. Finiteness near the origin. Fix ρ ∈ (0, r₁) and put T := η_ρ(D). By blowup_scaling with R = 2,
 H^n(T ∩ B̄_2(0)) = ((ENNReal.ofReal ρ)⁻¹)^n · H^n(D ∩ B̄_{2ρ}(x)).
The first factor is finite because ρ > 0. The second is at most H^n(D ∩ B̄_{r₀}(x)) < ∞, because 2ρ < r₀. Hence H^n(T ∩ B̄_2(0)) < ∞.
4. Integrability. φ is continuous, hence strongly measurable. Pointwise |φ| ≤ 1_{B̄_2(0)}, because φ ≤ 1 and φ = 0 off B̄_2(0). The indicator 1_{B̄_2(0)} is integrable for H^n⌞T, since B̄_2(0) is Borel and (H^n⌞T)(B̄_2(0)) = H^n(T ∩ B̄_2(0)) < ∞. So φ is integrable for H^n⌞T (Integrable.mono').
5. Comparison with the test integral. Pointwise 1_{B̄_1(0)} ≤ φ, since φ = 1 on B̄_1(0) and φ ≥ 0 elsewhere. Hence
 H^n(T ∩ B̄_1(0)) = ∫⁻ 1_{B̄_1(0)} d(H^n⌞T) ≤ ∫⁻ ofReal(φ) d(H^n⌞T) = ofReal(∫ φ d(H^n⌞T)) = ofReal(I(ρ)) ≤ ofReal(C).
This uses lintegral_indicator_one, lintegral_mono, ofReal_integral_eq_lintegral_ofReal (φ is integrable and ≥ 0), and I(ρ) < C.
6. Rescaling back. By blowup_scaling with R = 1 (ρ · 1 = ρ),
 H^n(T ∩ B̄_1(0)) = ((ENNReal.ofReal ρ)⁻¹)^n · H^n(D ∩ B̄_ρ(x)).
Now ((ofReal ρ)⁻¹)^n = ((ofReal ρ)^n)⁻¹ and (ofReal ρ)^n ∈ (0, ∞). Multiplying by (ofReal ρ)^n gives
 H^n(D ∩ B̄_ρ(x)) = (ofReal ρ)^n · H^n(T ∩ B̄_1(0)) ≤ (ofReal ρ)^n · ofReal(C) = ofReal(C · ρ^n).
The last equality is ofReal(C·ρ^n) = ofReal(C)·ofReal(ρ)^n, valid since C ≥ 0 and ρ ≥ 0 (ENNReal.ofReal_mul, ENNReal.ofReal_pow).
7. Conclusion. C = |Λ| + 1 and r₁ from step 2 satisfy the claim. The Borel hypothesis on D is not used. ∎

## Key steps

1. Cutoff φ = max(0, min(1, 2 − ‖w‖)) ∈ C_c with 1_{B̄_1(0)} ≤ φ ≤ 1_{B̄_2(0)}.
2. The tangent hypothesis gives ∫_{η_ρ(D)} φ → Λ := ∫_Q φ; choose r₁ with ∫_{η_ρ(D)} φ < |Λ| + 1 and ρ < r₀/2 on (0, r₁).
3. blowup_scaling (R = 2) gives H^n(η_ρ(D) ∩ B̄_2(0)) < ∞, so φ is integrable on η_ρ(D).
4. H^n(η_ρ(D) ∩ B̄_1(0)) ≤ ∫_{η_ρ(D)} φ ≤ |Λ| + 1.
5. blowup_scaling (R = 1) gives H^n(D ∩ B̄_ρ(x)) = ρ^n H^n(η_ρ(D) ∩ B̄_1(0)) ≤ (|Λ| + 1)ρ^n.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n 'HasApproximateTangentSpaceAt|blowUpMap|ae_tendsto_measure_inter_div|approxTangent|tangent_iff' project --glob '*.lean'`
- `rg -n 'ptd_|rsdic_|regcomp_|dor_lmb_' project --glob '*.lean' (no match)`
- `rg -n 'notation.*μHE|def euclideanHausdorffMeasure|theorem euclideanHausdorffMeasure_homothety_image|theorem Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_smul₀|theorem ae_tendsto_measure_inter_div|instance.*HasBesicovitchCovering|theorem countable_cover_nhdsWithin' mathlib/Mathlib`
- `rg -n 'theorem setIntegral_sdiff|theorem norm_setIntegral_le_of_norm_le_const |theorem tendsto_nhds_zero|theorem ofReal_integral_eq_lintegral_ofReal|theorem mem_nhdsGT_iff_exists_Ioo_subset|theorem squeeze_zero_norm'|theorem bounded_above_of_compact_support|theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem lintegral_indicator_one|theorem ae_restrict_mem|theorem ae_ball_iff|theorem div_le_of_le_mul|theorem le_of_add_le_add_right' mathlib/Mathlib`
- `grep -rn 'def HasApproximateTangentSpaceAt|def blowUpMap|abbrev Euclid' lake-packages-25730c7c/simongmt/Poincare/SimonGMT (SimonGMT 2b3663083f)`
- `git show a157a5f4f62ba1c354a3b0cc070d947560abf2e6:GMT/Ch07/Submission.lean; python3 -I exact-string comparison of the five child types with the accepted rsdic_* lean_statements in dag.json (all identical)`
- `python3 -I scans of dag.json lean_names (604) and all nodes/*/decomposition-v*.json proposal names (850) for the five ptd_tl_* names; grep -c ptd_tl over the eight chapter dag.json files; git for-each-ref (2,895 refs) | xargs git grep -l ptd_tl -- GMT; git log --all -S ptd_tl (all no match)`
- `python3 -I gmt-compare.py contract_scope(GMT/Ch07/Contract.lean, 'GMT.Ch07.main_theorem'); lake env lean /tmp/ptd-tl-decomp/Challenge_{blowup_scaling,ae_excess,tangent_growth,excess_density,pointwise_comparison,parent}.lean`
- `lake env lean /tmp/ptd-tl-decomp/Full.lean (#print axioms); Assembly.lean; GrowthVariant.lean; Instances.lean (pp.explicit)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the five child types and the parent type`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-48c739e201/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-locality-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-approx-tangent-locality-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ptd-tl-decomp/Full.lean`
- `/tmp/ptd-tl-decomp/Assembly.lean`
- `/tmp/ptd-tl-decomp/GrowthVariant.lean`
- `/tmp/ptd-tl-decomp/Instances.lean`
- `/tmp/ptd-tl-decomp/Challenge_parent.lean`

No proof of this statement or of any child is in the snapshot.
- GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean are byte-identical. They supply only the definitions: HasApproximateTangentSpaceAt (opened from SimonGMT) and approxTangentPlane.
- GMT/Ch03/Contract.lean records Simon 3.1.6 only as an unproved Prop.
- The rg search for ptd_/rsdic_/regcomp_/dor_lmb_ in project finds nothing.
- SimonGMT 2b3663083f (Chapter03/Rectifiable.lean) defines blowUpMap x r y = r⁻¹ • (y − x). It defines HasApproximateTangentSpaceAt as finrank P = n ∧ ∀ f : C_c(E, ℝ), Tendsto (r ↦ ∫ y in blowUpMap x r '' M, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 (∫ y in P, f y ∂μHE[n])).

Every library fact the child proofs cite exists in the pinned Mathlib 25730c7c with compatible hypotheses:
- density and covers: Besicovitch.ae_tendsto_measure_inter_div (Covering/Besicovitch.lean:1105, needs IsLocallyFiniteMeasure), instHasBesicovitchCovering, TopologicalSpace.countable_cover_nhdsWithin;
- Hausdorff measure: μHE[d] := euclideanHausdorffMeasure (Geometry/Euclidean/Volume/Measure.lean:72), Isometry.euclideanHausdorffMeasure_image, MeasureTheory.euclideanHausdorffMeasure_homothety_image (‖c‖₊ ^ d •), Measure.euclideanHausdorffMeasure_smul₀;
- set integrals: setIntegral_sdiff, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, norm_setIntegral_le_of_norm_le_const, ofReal_integral_eq_lintegral_ofReal, lintegral_indicator_one;
- filters and limits: mem_nhdsGT_iff_exists_Ioo_subset, ENNReal.tendsto_nhds_zero;
- ENNReal arithmetic: ENNReal.div_le_of_le_mul, ENNReal.le_of_add_le_add_right;
- a.e. bookkeeping: ae_restrict_mem, ae_ball_iff.

The identical frozen type has a complete, comparator-accepted Lean proof in commit a157a5f4. Its five helper types match the proposed children character for character. Porting them under fresh ptd_tl_ names compiles in the replayed comparator scope with only propext, Classical.choice and Quot.sound.
