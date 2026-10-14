# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.im_closure-a1`
- Child DAG node: `root.integrality_weak_limits-a1.im_closure-a1.lebesgue_points-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P := Eucl P. H := Hᵏ := μHE[k], Mathlib's normalized k-dimensional Hausdorff measure on ℝ^P (a Borel measure). B̄_s(x) := closedBall x s and B_s(x) := ball x s. For r > 0, ofReal((r^k)⁻¹) = r^{−k}. ‖t‖ₑ = |t| ∈ [0, ∞] for t ∈ ℝ. For a Borel measure λ on ℝ^P, Θ*ᵏ(λ, x) := dimensionalUpperDensity λ.toOuterMeasure (k : ℝ) univ x = limsup_{s↓0} λ(B̄_s(x)) / (ω_k · ofReal(s)^k), where ω_k := realUnitBallVolume k ∈ (0, ∞).

Source. This combines preliminary (v) and property (G2) of the parent proof: normalized Lebesgue points via the Lebesgue–Besicovitch differentiation theorem (Simon Ch. 1, 3.23 with the Symmetric Vitali Property 3.11(3); Mathlib's Besicovitch Vitali family), with Θ*ᵏ < ∞. Finiteness of the upper density is obtained from the sibling `rectifiability_density_comparison` (Simon Ch. 1, 3.3: if V is open, A ⊆ V and t ≤ Θ*ᵏ(λ, x) on A, then t·H(A) ≤ λ(V)). This replaces the tangent-plane argument (vi) of the parent proof and needs no tangent plane.

Statement. Let U ⊆ ℝ^P be open and M ⊆ U be H-null-measurable, with H(M ∩ K) < ∞ for every compact K ⊆ U. Let f : ℝ^P → ℝ be H-integrable on M ∩ K for every compact K ⊆ U. Then for H⌞M-a.e. x and every R > 0:
  r^{−k} ∫⁻_{M ∩ B̄_{Rr}(x)} ‖f(y) − f(x)‖ₑ dH(y) → 0 as r ↓ 0.

1. (Countable cover by relatively compact balls.)
   - If U = ∅ then M = ∅ and H⌞M = 0, so there is nothing to prove.
   - The balls B_s(y) with s > 0 and B̄_s(y) ⊆ U cover U. By second countability of ℝ^P, countably many of them, W_i := B_{s_i}(y_i) (i ∈ ℕ), cover U (`TopologicalSpace.isOpen_sUnion_countable`).
   - K_i := B̄_{s_i}(y_i) is compact with W_i ⊆ K_i ⊆ U.
   - Since M ⊆ U = ⋃_i W_i, and a countable union of H⌞M-null sets is H⌞M-null, it suffices to fix i and prove the claim for H⌞M-a.e. x ∈ W_i. Write W := W_i and K := K_i.

2. (A finite measure.)
   - λ := H⌞(M ∩ K) is a finite Borel measure on ℝ^P, since λ(ℝ^P) = H(M ∩ K) < ∞.
   - f is λ-integrable, by the hypothesis with this K.
   - For x ∈ W and s > 0 with B̄_s(x) ⊆ W ⊆ K: λ(B̄_s(x)) = H(M ∩ B̄_s(x)), and ∫⁻_{B̄_s(x)} ‖f − f(x)‖ₑ dλ = ∫⁻_{M ∩ B̄_s(x)} ‖f − f(x)‖ₑ dH. Here λ⌞B̄_s(x) = H⌞(B̄_s(x) ∩ M ∩ K) by `Measure.restrict_restrict` (closed balls are measurable), and B̄_s(x) ∩ M ∩ K = M ∩ B̄_s(x).

3. (Lebesgue–Besicovitch differentiation.)
   - λ is finite, hence locally finite and s-finite, and ℝ^P has the Besicovitch covering property (finite-dimensional normed space).
   - Apply Mathlib's `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div` to the Vitali family `Besicovitch.vitaliFamily λ` and the λ-integrable (hence locally integrable) f. Compose with `Besicovitch.tendsto_filterAt λ x`: closed balls B̄_s(x), s ↓ 0, tend to the Vitali filter at x.
   - This gives a λ-null set N such that for every x ∉ N:
     a_x(s) := (∫⁻_{B̄_s(x)} ‖f − f(x)‖ₑ dλ) / λ(B̄_s(x)) → 0 as s ↓ 0.
   - λ(N) = 0 means H(N ∩ M ∩ K) = 0, since M ∩ K is null-measurable (`Measure.restrict_apply₀'`). Hence H⌞M(N ∩ W) = 0.

4. (Finite upper density.)
   - Let A_∞ := {x ∈ W : Θ*ᵏ(λ, x) = ∞}.
   - For every real t > 0: A_∞ ⊆ W, W is open, and t ≤ Θ*ᵏ(λ, x) for x ∈ A_∞. The sibling `rectifiability_density_comparison` gives t·H(A_∞) ≤ λ(W) ≤ λ(ℝ^P) < ∞.
   - If H(A_∞) > 0, then t·H(A_∞) > λ(ℝ^P) for all large real t (also when H(A_∞) = ∞), a contradiction. So H(A_∞) = 0, hence H⌞M(A_∞) = 0.

5. (Good points.) Let x ∈ M ∩ W with x ∉ N ∪ A_∞, and fix R > 0.
   - Θ*ᵏ(λ, x) < ∞, so choose a real C > 0 with Θ*ᵏ(λ, x) < C. By the definition of limsup (`Filter.eventually_lt_of_limsup_lt`), eventually for s ↓ 0, λ(B̄_s(x))/(ω_k s^k) < C, i.e. λ(B̄_s(x)) ≤ C ω_k s^k.
   - Since Rr ↓ 0 as r ↓ 0 and W is open, for all sufficiently small r > 0 the radius s := Rr satisfies both this bound and B̄_s(x) ⊆ W.
   - For such r, put I(r) := ∫⁻_{M ∩ B̄_{Rr}(x)} ‖f − f(x)‖ₑ dH = ∫⁻_{B̄_s(x)} ‖f − f(x)‖ₑ dλ (step 2). Then I(r) ≤ λ(B̄_s(x)) · a_x(s):
     · if 0 < λ(B̄_s(x)) < ∞, this is an equality by the definition of a_x(s) (`ENNReal.div_mul_cancel`);
     · if λ(B̄_s(x)) = 0, then λ⌞B̄_s(x) = 0 and I(r) = 0.
   - Therefore r^{−k} I(r) ≤ r^{−k} · C ω_k (Rr)^k · a_x(Rr) = (C ω_k R^k) · a_x(Rr).
   - The right side tends to (C ω_k R^k) · 0 = 0 as r ↓ 0. This is step 3 composed with r ↦ Rr, which maps 𝓝[>] 0 to 𝓝[>] 0, together with `ENNReal.Tendsto.const_mul`, using C ω_k R^k ≠ ∞.
   - By the squeeze theorem in [0, ∞] (`tendsto_of_tendsto_of_tendsto_of_le_of_le'`, lower bound 0), r^{−k} I(r) → 0.

6. (Conclusion.) By steps 3–4, H⌞M-a.e. x ∈ W is a good point in the sense of step 5. By step 1 the claim holds for H⌞M-a.e. x. ∎

Formalization notes (a complete Lean proof of exactly this statement, inside the single theorem, compiled in a scratch build of frozen commit d8d46c9 with the sibling as a stub):
- Cover: `TopologicalSpace.isOpen_biUnion_countable` over {p | closedBall p.1 p.2 ⊆ U}, `ae_ball_iff`, `ae_restrict_iff'₀`.
- Finite measure: `isFiniteMeasure_restrict`, then `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div (Besicovitch.vitaliFamily λ)` with `Integrable.locallyIntegrable`, composed with `Besicovitch.tendsto_filterAt λ x`.
- Density bound: `Filter.eventually_lt_of_limsup_lt`; `dimensionalUpperDensity` unfolds by defeq.
- Step 4 can apply the sibling directly with t := ⊤: ⊤·H(A_∞) ≤ λ(ball) < ⊤ gives H(A_∞) = 0.
- Arithmetic: `ENNReal.mul_div_cancel'` covers both λ(B̄) = 0 and 0 < λ(B̄) < ∞; also `ENNReal.div_lt_iff`, `ENNReal.Tendsto.const_mul`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`.
- Pitfalls: the root-level name is `eventually_closedBall_subset`; root `zero_le` takes its argument implicitly; use `have` (not `haveI`) for the IsFiniteMeasure instance.

## Key steps

1. Cover U by countably many balls W_i whose closed balls K_i are compact subsets of U; it suffices to treat one W = W_i, K = K_i.
2. λ := Hᵏ⌞(M ∩ K) is a finite Borel measure and f ∈ L¹(λ); Lebesgue–Besicovitch differentiation (Mathlib, Besicovitch Vitali family along closed balls) gives λ(B̄_s(x))⁻¹∫⁻_{B̄_s(x)} |f − f(x)| dλ → 0 for λ-a.e. x.
3. The sibling rectifiability_density_comparison gives Θ*ᵏ(λ, x) < ∞ for Hᵏ-a.e. x ∈ W, hence λ(B̄_s(x)) ≤ C ω_k s^k for small s.
4. For small r, r^{−k}∫⁻_{M∩B̄_{Rr}(x)} |f − f(x)| dHᵏ ≤ C ω_k R^k · (the λ-average over B̄_{Rr}(x)) → 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical); cmp workspace Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (identical)`
- `python3 dag.json scans (re-run just before submission): status/candidate_commit/lean_statement/title/statement of rectifiability_density_comparison, slicing_representation_unique, ltg_tau_integrable, fiw_ims_frame_sign, fiw_ims_orientation_sign, iwl_restriction_theory, iwl_weighted_tangent_locality, lpf_wtc_ae_zero_density_off_set, br_weightedTangent_congr; regex scan of all accepted nodes for Lebesgue|IsMeasureRepresentation|tauAction|HasWeightedApproximateTangentSpaceAt|density; reserved names (no iwl_imc_*)`
- `sed -n 6532,6575p and 2364,2368p /runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/runtime.py (_existing_lean_name_problem / _accepted_checkpoint: why attempt 1's lpf reuse was rejected)`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem HasWeightedApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity|realUnitBallVolume' simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div|theorem tendsto_filterAt|protected def vitaliFamily' mathlib/Mathlib/MeasureTheory/Covering/{Differentiation,Besicovitch}.lean (Differentiation.lean:818, Besicovitch.lean:1021 and 1060)`
- `grep -rn 'theorem withDensity_apply |theorem setLIntegral_measure_zero|theorem _root_.Set.measure_eq_iInf_isOpen|theorem nullMeasurableSet_eq_fun' mathlib/Mathlib/MeasureTheory (found in Measure/WithDensity.lean:44, Integral/Lebesgue/Basic.lean:478, Measure/Regular.lean:368, Function/StronglyMeasurable/AEStronglyMeasurable.lean:575)`
- `sed -n 724,770p book/chapter-06.txt (Simon Ch. 6, 3.1 and 3.2 Remarks (1)-(3)); grep -n "3.3 Theorem|3.6 Theorem|3.7 Remarks" book/chapter-01.txt`
- `verifier/gmt-compare.py child_modules (contract mode) + verifier/lean_contract.validate_lean_statement on all 11 child types and the parent`
- `lean v4.35.0-rc3 (LEAN_PATH scratch build + lake-packages-25730c7c): lean -o build3/GMT/Ch06/Submission.olean src3/Submission.lean; lean checks/NodeChallenge_00..11.lean (frozen build) and checks/NodeSolution_00..11.lean (build3) with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/imc-decomp-v2/src3/Submission.lean`
- `/tmp/imc-decomp-v2/logs/src3.out`
- `/tmp/imc-decomp-v2/checks/NodeSolution_11.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract, and Submission is byte-identical to it.

Available tools:
- SimonGMT: HasWeightedApproximateTangentSpaceAt (Ch. 3, 1.7, a limit over blow-ups, so it is invariant under a nonzero constant factor), its uniqueness lemma, CountablyRectifiable.mono / countablyRectifiable_iUnion, dimensionalUpperDensity and realUnitBallVolume.
- Mathlib (imported via Covering.DensityTheorem): Lebesgue–Besicovitch differentiation (VitaliFamily.ae_tendsto_lintegral_enorm_sub_div with Besicovitch.vitaliFamily / tendsto_filterAt), withDensity, outer regularity of finite measures, and AEStronglyMeasurable.nullMeasurableSet_eq_fun.
- The contract does not import SimonGMT's Chapter01.DensityComparison. Density comparison is therefore taken from the accepted Submission theorem rectifiability_density_comparison, and the Upper Density Theorem is the new child iwl_imc_density_zero_off_set.

Controller code (runtime.py) explains the rejected attempt: reuse requires an accepted checkpoint in the controller's view. The replacement child sidesteps the reservation on lpf_wtc_ae_zero_density_off_set.

Scratch Lean results (/tmp/imc-decomp-v2):
- All 11 child types and the parent elaborate in the exact comparator child scope.
- Complete single-theorem proofs of the 6 new children compile.
- The parent assembles from the children plus iwl_weighted_tangent_locality and iwl_restriction_theory.
- Axiom footprints are [propext, Classical.choice, Quot.sound] plus the intended stubs.
