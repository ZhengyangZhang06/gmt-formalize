# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_current-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_current-a1.bounded_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the supplied proof of cmc_fc_series_current, whose step-6 bound is the hypothesis (H) below (Simon Ch. 6, proof of 7.2: the M-absolutely convergent series "define" currents, chapter-06.txt lines 2119–2123; the topology of 𝒟ⁿ(U), chapter-06.txt lines 170–176). This isolates the fact that a linear functional bounded by A·sup_x |ω(x)| is sequentially continuous, i.e. a current. Notation: N(α) := covectorEuclideanNorm α; ω(x) := (ω : DifferentialForm (Euclid P) n) x; ‖·‖ is the operator norm on Covector (Euclid P) n. Hypothesis (H): |L(ω)| ≤ c·A whenever ω ∈ 𝒟ⁿ(U), c > 0 and N(ω(x)) ≤ c for all x. Sibling theorems: norm_props = Submission.rsd_mw_tfa_norm_props (only conjunct (iii) is used) and uniform_small = Submission.dpf_pfc_testFormOnConverges_zero_uniform.
1. (A ≥ 0.) Apply (H) to ω = 0 and c = 1. The zero test form has N(0(x)) = N(0) = 0 ≤ 1 (SimonGMT covectorEuclideanNorm_zero), and L(0) = 0 by linearity, so 0 = |L(0)| ≤ 1·A = A.
2. (The constant C.) By norm_props (iii) applied to P and n, there is C ∈ ℝ with C ≥ 0 and N(α) ≤ C·‖α‖ for every α ∈ Covector (Euclid P) n.
3. (Sequential continuity of L.) Let ωs : ℕ → 𝒟ⁿ(U) with TestFormOnConverges ωs 0. By uniform_small (applied to P, n, U, ωs), for every ε > 0, for all sufficiently large j, ‖ωs_j(x)‖ ≤ ε for all x. Let η > 0 and put ε := η / (2(C + 1)(A + 1)); then ε > 0, since η > 0, C + 1 ≥ 1 and A + 1 ≥ 1 (steps 1–2). Choose j₀ with ‖ωs_j(x)‖ ≤ ε for all j ≥ j₀ and all x. For j ≥ j₀ and every x, N(ωs_j(x)) ≤ C·‖ωs_j(x)‖ ≤ C·ε ≤ (C + 1)·ε, using C ≥ 0 and ε > 0. Since (C + 1)·ε > 0, (H) with c := (C + 1)·ε gives |L(ωs_j)| ≤ (C + 1)·ε·A. Now (C + 1)·ε·(A + 1) = η/2, and (C + 1)·ε > 0 with A ≤ A + 1, so (C + 1)·ε·A ≤ (C + 1)·ε·(A + 1) = η/2 < η. Hence dist(L(ωs_j), 0) = |L(ωs_j)| < η for all j ≥ j₀. Since η > 0 was arbitrary, L(ωs_j) → 0 as j → ∞ (Metric.tendsto_atTop). (This is the estimate of step 7 of the supplied proof, |Y(ω_k)| ≤ (N·ε_k + 1/(k+1))·s → 0, written with an explicit ε and j₀.)
4. (The current.) A GeometricCurrentOn U n is a structure with fields toCurrent : TestFormOn U n →ₗ[ℝ] ℝ and continuous' : for every ωs with TestFormOnConverges ωs 0, toCurrent(ωs_j) → 0 in ℝ. Step 3 is exactly continuous' for toCurrent := L. Put Y := ⟨L, step 3⟩. Its coercion to a function is Y.toCurrent = L, so Y(ω) = L(ω) for every ω ∈ 𝒟ⁿ(U) (definitionally). ∎
Lean note (a compiled route, about 30 lines): `obtain ⟨C, hC0, hC⟩ := (hnorm P n).2.2.1`; `have hA : 0 ≤ A := by simpa using hL 0 1 one_pos (fun x => by simp)`; `refine ⟨⟨L, fun ωs hωs => ?_⟩, fun ω => rfl⟩`; `obtain ⟨K, -, -, -, hunif⟩ := hsmall P n U ωs hωs`; `rw [Metric.tendsto_atTop]`; `set ε : ℝ := η / (2 * (C + 1) * (A + 1))`; `obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif ε hεpos)`; bound N(ωs_j(x)) with `hC`, `mul_le_mul_of_nonneg_left` and `nlinarith`; `rw [Real.dist_eq, sub_zero]`; `field_simp` proves (C + 1) * ε * (A + 1) = η / 2, and `nlinarith` closes (C + 1) * ε * A < η.

## Key steps

1. (H) at ω = 0, c = 1 gives A ≥ 0; norm_props (iii) gives C ≥ 0 with |α| ≤ C‖α‖.
2. If ωs → 0 in 𝒟ⁿ(U), uniform_small gives eventually ‖ωs_j(x)‖ ≤ ε for all x, hence |ωs_j(x)| ≤ (C + 1)ε.
3. (H) gives |L(ωs_j)| ≤ (C + 1)εA ≤ η/2 < η for ε = η/(2(C + 1)(A + 1)), so L(ωs_j) → 0.
4. Y := ⟨L, continuity⟩ is a current with Y(ω) = L(ω).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cat local-references/123e8435b4a2469b/manifest.json`
- `rg -n "covectorEuclideanNorm|massAdmissibleOn|TestFormOnConverges|GeometricCurrentOn.mass" local-references/123e8435b4a2469b/project/GMT --glob '*.lean' (no match)`
- `rg -n "theorem ENNReal.ofReal_tsum_of_nonneg|theorem summable_toReal|theorem tsum_toReal_eq|theorem ne_top_of_tsum_ne_top|theorem Summable.of_norm_bounded |theorem Summable.of_nonneg_of_le|theorem norm_tsum_le_tsum_norm|theorem tsum_mul_left|theorem ofReal_le_iff_le_toReal" local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `rg -n "bounded_above_of_compact_support|theorem comp_left|ofReal_max|theorem tendsto_atTop" local-references/123e8435b4a2469b/mathlib/Mathlib --glob '*.lean'`
- `grep -n 'covectorEuclideanNorm|massAdmissibleOn|massOn|le_massOn' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'GeometricCurrentOn|TestFormOnConverges|testFormOnSubmodule' Chapter06/Currents.lean; grep -n 'IsSmoothForm|IsTestForm' Chapter06/Forms.lean; head Chapter06/FormSupNorm.lean; grep -n import Chapter06/*.lean`
- `python3 scans of dag.json: lean_statements mentioning covectorEuclideanNorm, massAdmissibleOn, TestFormOnConverges, '→ₗ[ℝ] ℝ' or mass/toReal bounds; exact-name lookups of rsd_mw_tfa_norm_props, dpf_pfc_testFormOnConverges_zero_uniform, cmr_abs_apply_le_massOn and cmc_fc_sc_testForm_coeff_bound / cmc_fc_sc_abs_le_mul_mass / cmc_fc_sc_current_of_coeff_bound`
- `git diff b4d606d f492ba4 -- GMT/Ch07/Submission.lean; git diff b4d606d 8d68dfd -- GMT/Ch07/Submission.lean (accepted proofs of the two reused theorems)`
- `sed -n 953,962p, 1659,1700p, 1801,2000p, 2364,2368p, 3159,3200p, 6532,6575p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; sed -n 179,214p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `sed -n 168,250p and 2105,2125p book/chapter-06.txt (Simon 6.1.14–1.15, 6.2.3–2.6, proof of 7.2)`
- `lake env lean GMT/Scratch/cmc_fc_series_current_decomposition/{Types,Api,Inst,Assembly,Children,Full,FullFromJson}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Ring.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-series-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-series-current-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-456fc8281b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmc_fc_series_current_decomposition/Types.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmc_fc_series_current_decomposition/Inst.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmc_fc_series_current_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmc_fc_series_current_decomposition/Children.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmc_fc_series_current_decomposition/FullFromJson.lean`

Snapshot and pinned packages:
- The snapshot (project b4d606db, mathlib 25730c7c) has a Contract.lean that is byte-identical to the workspace Contract.lean and Submission.lean.
- The snapshot project has no match for the series and mass-estimate objects. They live in the pinned SimonGMT package:
  - covectorEuclideanNorm, massAdmissibleOn and GeometricCurrentOn.massOn/mass/le_massOn in Chapter06/Mass.lean;
  - GeometricCurrentOn and TestFormOnConverges in Chapter06/Currents.lean;
  - IsSmoothForm := ContDiff ℝ ∞ in Forms.lean.
- testFormEuclideanSupNorm in FormSupNorm.lean is outside the contract's import closure and is not used.

Mathlib lemmas: the pinned Mathlib supplies every summation, ENNReal and boundedness lemma the proofs cite. These were #check-ed after import GMT.Ch07.Submission:
- ENNReal: ne_top_of_tsum_ne_top, summable_toReal, tsum_toReal_eq, ofReal_tsum_of_nonneg, ofReal_le_iff_le_toReal, ofReal_max;
- Summable: of_norm_bounded, of_nonneg_of_le, tsum_add, tsum_le_tsum, hasSum;
- also norm_tsum_le_tsum_norm, tsum_mul_left, Continuous.bounded_above_of_compact_support, HasCompactSupport.comp_left and Metric.tendsto_atTop.
- A bare `tsum_add` does not exist in this Mathlib; Summable.tsum_add does.

DAG declarations:
- The comparator-accepted rsd_mw_tfa_norm_props and dpf_pfc_testFormOnConverges_zero_uniform are reused with identical frozen types; their proofs are in commits f492ba4 and 8d68dfd.
- cmr_abs_apply_le_massOn is unaccepted and under another parent, so it is not reusable.
- The three new cmc_fc_sc_* names are fresh.

Lean result: all child types elaborate, and the parent's exact type is proved end to end from them using only the axioms propext, Classical.choice and Quot.sound.
