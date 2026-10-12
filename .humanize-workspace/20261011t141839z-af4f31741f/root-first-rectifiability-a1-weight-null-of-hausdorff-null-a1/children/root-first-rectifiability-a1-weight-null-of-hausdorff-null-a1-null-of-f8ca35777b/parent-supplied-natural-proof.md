# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1`
- Child DAG node: `root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1.null_of_ball_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–5 of the parent-supplied proof of frt_weight_null_of_hausdorff_null. This is the covering comparison behind Simon Ch. 8, 1.2, i.e. the null case of the Rogers–Taylor upper-density comparison. Compared with the parent, the piece Z_{k,j}, the constant (k+1)ω_n and the scale 1/j are replaced by an arbitrary set A, an arbitrary finite constant c and an arbitrary scale δ > 0.

Notation.
- B_ρ(x) := closedBall x ρ. For real ρ, 'ρ^n' means ENNReal.ofReal(ρ)^n.
- μH[n] is Mathlib's unnormalised Hausdorff measure with real exponent n.
- H^n := μHE[n] = c_n • μH[n], where c_n := addHaarScalarFactor volume μH[n] ∈ ℝ≥0 and c_n ≠ 0 (Measure.euclideanHausdorffMeasure_def, Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero; Geometry/Euclidean/Volume/Measure.lean:74, 96).
- diam is the extended diameter ediam. Powers of elements of [0, ∞] are ENNReal powers, so 0^0 = 1, 0^n = 0 for n ≥ 1, and d^(n:ℝ) = d^n (ENNReal.rpow_natCast).
- For t ⊆ ℝ^N put s(t) := ⨆_{t ≠ ∅} diam(t)^n. So s(t) = diam(t)^n if t ≠ ∅, and s(t) = 0 if t = ∅.
- μ applied to an arbitrary set is its outer measure, which is monotone and countably subadditive. No measurability of A is used.

1. μH[n](A) = 0. Indeed 0 = H^n(A) = c_n · μH[n](A), and c_n ≠ 0.

2. One covering set. Let t ⊆ ℝ^N with diam t ≤ ENNReal.ofReal δ. Claim: μ(t ∩ A) ≤ c · s(t).
 (a) If t ∩ A = ∅, then μ(t ∩ A) = 0 ≤ c · s(t).
 (b) Otherwise fix x ∈ t ∩ A. Then t ≠ ∅, so s(t) = diam(t)^n. Since diam t ≤ ofReal δ < ∞, the number d := (diam t).toReal is real, satisfies 0 ≤ d ≤ δ, and ENNReal.ofReal d = diam t. For y ∈ t we have edist y x ≤ diam t (Metric.edist_le_ediam_of_mem), hence dist y x ≤ d. Consequently t ∩ A ⊆ t ⊆ B_r(x) for every real r ≥ d.
  (b1) Case d > 0. Since 0 < d ≤ δ and x ∈ A, the hypothesis gives μ(t ∩ A) ≤ μ(B_d(x)) ≤ c · ofReal(d)^n = c · diam(t)^n = c · s(t).
  (b2) Case d = 0 and n = 0. Take ρ := δ, which satisfies 0 < δ ≤ δ and δ ≥ d. Then μ(t ∩ A) ≤ μ(B_δ(x)) ≤ c · ofReal(δ)^0 = c = c · diam(t)^0 = c · s(t).
  (b3) Case d = 0 and n ≥ 1. Then diam t = 0. For every ρ ∈ (0, δ) we have t ∩ A ⊆ B_ρ(x), so μ(t ∩ A) ≤ μ(B_ρ(x)) ≤ c · ofReal(ρ)^n. As ρ → 0⁺:
   - ofReal(ρ) → ofReal(0) = 0, by continuity of ENNReal.ofReal;
   - ofReal(ρ)^n → 0^n = 0, by continuity of a ↦ a^n on [0, ∞] (ENNReal.continuous_pow);
   - c · ofReal(ρ)^n → c · 0 = 0, because c ≠ ∞ (ENNReal.Tendsto.const_mul).
   Thus the constant μ(t ∩ A) is, for all ρ ∈ (0, δ) (a set in 𝓝[>] 0), at most a function tending to 0. Hence μ(t ∩ A) ≤ 0 (ge_of_tendsto), and 0 = c · 0^n = c · diam(t)^n = c · s(t).

3. Good covers. Let ζ ∈ (0, ∞]. By Measure.hausdorffMeasure_apply (MeasureTheory/Measure/Hausdorff.lean:546),
 μH[n](A) = ⨆_{r > 0} ⨅ { Σ_{k∈ℕ} s(t_k) : (t_k)_{k∈ℕ} with A ⊆ ⋃_k t_k and diam t_k ≤ r for all k }.
 The term with r := ENNReal.ofReal δ (which is > 0 because δ > 0) is at most the supremum, which is 0 by step 1. So this infimum equals 0 < ζ. Therefore there is a sequence (t_k)_{k∈ℕ} of subsets of ℝ^N such that A ⊆ ⋃_k t_k, diam t_k ≤ ofReal δ for every k, and Σ_k s(t_k) < ζ.

4. Summation. Since A ⊆ ⋃_k t_k, every y ∈ A lies in some t_k ∩ A, i.e. A ⊆ ⋃_k (t_k ∩ A). By monotonicity, countable subadditivity (measure_iUnion_le) and step 2 applied to each t_k:
 μ(A) ≤ Σ_k μ(t_k ∩ A) ≤ Σ_k c · s(t_k) = c · Σ_k s(t_k) ≤ c · ζ,
 where the equality is ENNReal.tsum_mul_left. Hence μ(A) ≤ c · ζ for every ζ > 0.

5. Conclusion.
- If c = 0, step 4 with ζ = 1 gives μ(A) ≤ 0 · 1 = 0.
- If c ≠ 0, let ε > 0. Since c ≠ ∞, ζ := ε / c satisfies ζ > 0 (ENNReal.div_pos) and c · (ε / c) = ε (ENNReal.mul_div_cancel). Step 4 then gives μ(A) ≤ ε. Since ε > 0 is arbitrary, μ(A) ≤ 0 (ENNReal.le_of_forall_pos_le_add).
In both cases μ(A) = 0. ∎

## Key steps

1. H^n(A) = c_n·μH[n](A) = 0 with c_n ≠ 0, so the unnormalised Hausdorff measure μH[n](A) vanishes.
2. Every t with diam t ≤ δ satisfies μ(t ∩ A) ≤ c·s(t), where s(t) = ⨆_{t≠∅} diam(t)^n. Pick x ∈ t ∩ A; then t ⊆ B_d(x) with d = diam t ≤ δ. If d > 0, apply the hypothesis at ρ = d. If d = 0 and n = 0, use ρ = δ. If d = 0 and n ≥ 1, let ρ ↓ 0, using c < ∞.
3. hausdorffMeasure_apply at scale r = ofReal δ > 0 gives, for each ζ > 0, a cover (t_k) of A with diam t_k ≤ δ and Σ_k s(t_k) < ζ.
4. Countable subadditivity gives μ(A) ≤ Σ_k μ(t_k ∩ A) ≤ c·Σ_k s(t_k) ≤ c·ζ for every ζ > 0.
5. Since c < ∞ (take ζ = ε/c, or handle c = 0 directly), μ(A) = 0.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json (project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch08/Submission.lean GMT/Ch08/Contract.lean <snapshot>/project/GMT/Ch08/Contract.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `grep -n "theorem\|lemma" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean (mkMetric_apply 464, hausdorffMeasure_apply 546, mkMetric_le_liminf_tsum 498)`
- `sed -n 1,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def 74, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 96)`
- `grep -rn "theorem_3_2\b\|3\.2(2)\|2 \^ n \* t\|upperDensity_le\b\|measure_le_.*hausdorff" .lake/packages/simongmt/Poincare/SimonGMT (no upper-density comparison)`
- `grep -rn "theorem.*[Uu]pperDensity.*le\|theorem .*le_.*UpperDensity" .lake/packages/simongmt/Poincare/SimonGMT (only DensityComparison.lean:251 lower comparison, HausdorffDensityBounds, RelativeDensityComparison)`
- `grep -n "^theorem\|^lemma" Chapter01/{HausdorffDensityBounds,HausdorffContentDensity,LowerDensityComparison,InfiniteDensitySet,EuclideanHausdorffUpper,Hausdorff}.lean`
- `rg -n 'exists_nat_one_div_lt|mem_nhdsGT_iff_exists_Ioo_subset|measure_ball_pos|measure_ball_lt_top|edist_le_ediam_of_mem|measure_iUnion_le|measure_mono_null|tsum_mul_left|continuous_pow|Tendsto.const_mul' mathlib/Mathlib/{Algebra/Order,Order/Filter,Topology,MeasureTheory}`
- `sed -n 419,423p Mathlib/Basic/ENNReal/Inv.lean; sed -n 611,624p Mathlib/Basic/ENNReal/Basic.lean; sed -n 186,189p Mathlib/Basic/ENNReal/Inv.lean (div_lt_iff, le_of_forall_pos_le_add, exists_nat_gt, mul_div_cancel)`
- `lake env lean /tmp/wnh_decomp_scratch/Where.lean (getModuleIdxFor?/findDeclarationRanges? for the 25 lemmas used by the child proofs)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on both child lean_statements: valid`
- `lake env lean /tmp/wnh_decomp_scratch/Ch_A.lean and Ch_B.lean (comparator NodeChallenge form): both elaborate`
- `lake env lean /tmp/wnh_decomp_scratch/Final.lean (parent assembly from sorry'd children closes the frozen parent type with no own sorry)`
- `lake env lean /tmp/wnh_decomp_scratch/ProveA.lean, ProveB.lean, FinalFull.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `grep -c 'frt_measure_null_of_hausdorff_null_ball_bound\|frt_ball_bound_of_finite_density' dag.json (0)`
- `sed -n 560,640p book/chapter-01.txt and sed -n 145,215p book/chapter-08.txt (Simon 2014 numbering: 3.2 remark, 3.3 lower comparison; book proof of 8.1.2)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffContentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-null-of-hausdorff-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`

Snapshot: project 63436ae6, Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract and Submission. Neither pinned SimonGMT nor Mathlib has the upper-density comparison (μ(A) ≤ C·H^n(A) under an upper bound on the density). SimonGMT has only the lower comparison 3.3 (DensityComparison.lean:251) and the 3.26 bounds, so child frt_measure_null_of_hausdorff_null_ball_bound is new. Its proof uses Measure.hausdorffMeasure_apply (Hausdorff.lean:546), Measure.euclideanHausdorffMeasure_def and Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Volume/Measure.lean:74/96), Metric.edist_le_ediam_of_mem (Diam.lean:47), measure_iUnion_le (OuterMeasure/Basic.lean:66), ENNReal.tsum_mul_left, ENNReal.continuous_pow, ENNReal.Tendsto.const_mul, ge_of_tendsto, ENNReal.le_of_forall_pos_le_add, ENNReal.mul_div_cancel, ENNReal.div_pos and ENNReal.rpow_natCast. Child frt_ball_bound_of_finite_density uses Metric.measure_ball_pos (OpenPos.lean:212), measure_ball_lt_top (Typeclasses/Finite.lean:373), ENNReal.exists_nat_gt (Basic/ENNReal/Basic.lean:622), mem_nhdsGT_iff_exists_Ioo_subset (LeftRightNhds.lean:104), exists_nat_one_div_lt (Archimedean/Basic.lean:211) and ENNReal.div_lt_iff (Basic/ENNReal/Inv.lean:421). Both child statements pass validate_lean_statement and elaborate in the comparator NodeChallenge scope. The parent assembly closes the frozen type with no sorry of its own. Complete scratch Lean proofs of both children check with only propext, Classical.choice and Quot.sound. Neither name collides with any node in dag.json.
