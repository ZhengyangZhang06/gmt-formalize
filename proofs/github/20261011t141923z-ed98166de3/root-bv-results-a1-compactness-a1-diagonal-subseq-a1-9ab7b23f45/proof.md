# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.compactness-a1`
- Child DAG node: `root.bv_results-a1.compactness-a1.diagonal_subseq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2, Theorem 2.6 (p. 50). The printed proof reduces the claim to precompactness in L¹_loc(U); this step turns precompactness on every compact subset into an L¹_loc-convergent subsequence by compact exhaustion and diagonal extraction. The argument below is step A2 of the reviewed proof supplied to node root.bv_results-a1.compactness-a1 (Section A of the parent root.bv_results-a1), specialized to this self-contained statement with the details filled in. Notation: ℝⁿ = Rn n = EuclideanSpace ℝ (Fin n), μ = volume (Lebesgue measure), ∫⁻ is the lower Lebesgue integral in [0,∞], ‖a‖ₑ ∈ [0,∞) the extended norm, ofReal = ENNReal.ofReal.

Statement recalled. U ⊆ ℝⁿ is open, every u_k is locally integrable on U, and (finite-net hypothesis) for every compact Q ⊆ U and every ε > 0 there is a finite F ⊆ ℕ such that every k has some j ∈ F with ∫⁻_Q ‖u_k − u_j‖ₑ < ofReal ε. Claim: there are a strictly increasing ψ : ℕ → ℕ and v : ℝⁿ → ℝ with v locally integrable on U and, for every compact K ⊆ U, ∫⁻_K ‖u_{ψ(k)} − v‖ₑ → 0 as k → ∞ (Chapter02.TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop).

0. L¹ spaces. For a measurable Q let L¹(Q) := Lp ℝ 1 (μ.restrict Q); it is a complete metric space (Lp.instCompleteSpace). If f is integrable on Q, write [f]_Q := MemLp.toLp f ∈ L¹(Q) (memLp_one_iff_integrable). For f, g integrable on Q, edist([f]_Q, [g]_Q) = eLpNorm(f − g, 1, μ.restrict Q) = ∫⁻_Q ‖f − g‖ₑ (Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm); consequently dist([f]_Q, [g]_Q) < ε whenever ∫⁻_Q ‖f − g‖ₑ < ofReal ε (ENNReal.toReal_lt_of_lt_ofReal). Every element g of L¹(Q) has a strongly measurable representative ⇑g (Lp.stronglyMeasurable) which is integrable on Q, with [⇑g]_Q = g.

1. Compact exhaustion. For j ∈ ℕ let Q_j := {x ∈ closedBall(0, j + 1) : ofReal(1/(j + 1)) ≤ infEDist(x, Uᶜ)} (Metric.infEDist; if Uᶜ = ∅ then infEDist(x, ∅) = ∞ and Q_j = closedBall(0, j + 1), so no case distinction is needed; if U = ∅ every Q_j is empty and everything below holds trivially).
 (a) Q_j is compact: it is closed (closedBall is closed and x ↦ infEDist(x, Uᶜ) is continuous, so the superlevel set is closed) and bounded in the proper space ℝⁿ.
 (b) Q_j ⊆ U: if x ∉ U then x ∈ Uᶜ, so infEDist(x, Uᶜ) = 0 < ofReal(1/(j + 1)).
 (c) Q_j ⊆ interior Q_{j+1}: for x ∈ Q_j the set O := {y : ‖y‖ < j + 2 ∧ ofReal(1/(j + 2)) < infEDist(y, Uᶜ)} is open (continuity), contains x (‖x‖ ≤ j + 1 < j + 2 and infEDist(x, Uᶜ) ≥ 1/(j + 1) > 1/(j + 2)) and is contained in Q_{j+1}. In particular Q_j ⊆ Q_{j+1}, so i ≤ j implies Q_i ⊆ Q_j.
 (d) Every x ∈ U lies in some Q_j: Uᶜ is closed and x ∉ Uᶜ = closure Uᶜ, so infEDist(x, Uᶜ) > 0 (Metric.mem_closure_iff_infEDist_zero), and for j large ‖x‖ ≤ j + 1 and 1/(j + 1) ≤ infEDist(x, Uᶜ).
 (e) Every compact K ⊆ U lies in some Q_j: by (c) and (d) the increasing open sets interior Q_{j+1} (j ∈ ℕ) cover K; a finite subcover exists by compactness and, the sets being increasing, K ⊆ interior Q_{J+1} ⊆ Q_{J+1} for some J (IsCompact.elim_directed_cover).

2. Total boundedness. Fix j. Each u_k is integrable on Q_j (LocallyIntegrableOn.integrableOn_compact_subset with (a), (b)). Put f_{j,k} := [u_k]_{Q_j} ∈ L¹(Q_j) and S_j := {f_{j,k} : k ∈ ℕ}. S_j is totally bounded (Metric.totallyBounded_iff): given ε > 0, the finite-net hypothesis for Q = Q_j gives a finite F with S_j ⊆ ⋃_{i ∈ F} ball(f_{j,i}, ε) by step 0. Hence closure S_j is totally bounded (TotallyBounded.closure) and closed in the complete space L¹(Q_j), so it is compact (TotallyBounded.isCompact_of_isClosed).

3. Nested subsequences. In a metric space every sequence in a compact set has a subsequence converging to a point of that set (IsCompact.tendsto_subseq). Define recursively strictly increasing maps ψ_j : ℕ → ℕ and elements g_j ∈ L¹(Q_j): choose ψ_0 strictly increasing with f_{0,ψ_0(k)} → g_0 in L¹(Q_0) (the sequence lies in S_0 ⊆ closure S_0); given ψ_j, the sequence k ↦ f_{j+1,ψ_j(k)} lies in S_{j+1} ⊆ closure S_{j+1}, so choose φ_{j+1} strictly increasing and g_{j+1} with f_{j+1,ψ_j(φ_{j+1}(k))} → g_{j+1}, and put ψ_{j+1} := ψ_j ∘ φ_{j+1}. Since a subsequence of a convergent sequence converges to the same limit, for i ≤ j the sequence k ↦ f_{i,ψ_j(k)} also converges to g_i (ψ_j = ψ_i ∘ φ_{i+1} ∘ ⋯ ∘ φ_j).

4. Diagonal. Put ψ(k) := ψ_k(k). A strictly increasing φ : ℕ → ℕ satisfies φ(m) ≥ m (StrictMono.id_le), so ψ(k + 1) = ψ_k(φ_{k+1}(k + 1)) ≥ ψ_k(k + 1) > ψ_k(k) = ψ(k); hence ψ is strictly increasing. Fix j. For k ≥ j, ψ_k = ψ_j ∘ χ_k with χ_k := φ_{j+1} ∘ ⋯ ∘ φ_k, so ψ(k) = ψ_j(m(k)) with m(k) := χ_k(k). Since ψ and ψ_j are strictly increasing, m is strictly increasing on {k ≥ j}, so m(k) → ∞, and therefore f_{j,ψ(k)} = f_{j,ψ_j(m(k))} → g_j in L¹(Q_j) as k → ∞. Let G_j := ⇑g_j (step 0). By step 0, e_j(k) := ∫⁻_{Q_j} ‖u_{ψ(k)} − G_j‖ₑ = edist(f_{j,ψ(k)}, g_j) → 0 (tendsto_iff_edist_tendsto_0).
 (Equivalent shortcut, convenient in Lean: the sequence k ↦ (f_{j,k})_{j∈ℕ} lies in ∏_j closure S_j, which is compact by Tychonoff (isCompact_univ_pi) and first countable as a countable product of metric spaces; IsCompact.tendsto_subseq gives one strictly increasing ψ along which every coordinate converges (tendsto_pi_nhds), which is exactly the conclusion of steps 3–4.)

5. Compatibility of the limits. Let i ≤ j, so Q_i ⊆ Q_j. All of u_{ψ(k)}, G_i, G_j are a.e.-strongly measurable on Q_i. By the triangle inequality for ‖·‖ₑ, additivity of ∫⁻ for a.e.-measurable summands and lintegral_mono_set,
   ∫⁻_{Q_i} ‖G_i − G_j‖ₑ ≤ ∫⁻_{Q_i} ‖G_i − u_{ψ(k)}‖ₑ + ∫⁻_{Q_i} ‖u_{ψ(k)} − G_j‖ₑ ≤ e_i(k) + e_j(k)
   for every k; the right side tends to 0, so ∫⁻_{Q_i} ‖G_i − G_j‖ₑ = 0, and therefore G_i = G_j μ-a.e. on Q_i (lintegral_eq_zero_iff').

6. Gluing. For x ∈ U let j(x) be the least j with x ∈ Q_j (it exists by 1(d)) and put v(x) := G_{j(x)}(x); for x ∉ U put v(x) := 0. Claim: for every j, v = G_j μ-a.e. on Q_j. Indeed Q_j is the finite union over i ≤ j of D_i := {x ∈ Q_j : j(x) = i} ⊆ Q_i (Q_j ⊆ U by 1(b)); on D_i we have v = G_i, and G_i = G_j a.e. on Q_i ⊇ D_i by step 5; a finite union of null sets is null.

7. Convergence. By step 6 and lintegral_congr_ae (for μ.restrict Q_j), ∫⁻_{Q_j} ‖u_{ψ(k)} − v‖ₑ = e_j(k) → 0 for every j. If K ⊆ U is compact, then K ⊆ Q_j for some j (1(e)), so 0 ≤ ∫⁻_K ‖u_{ψ(k)} − v‖ₑ ≤ ∫⁻_{Q_j} ‖u_{ψ(k)} − v‖ₑ (lintegral_mono_set), and the squeeze theorem gives ∫⁻_K ‖u_{ψ(k)} − v‖ₑ → 0. This is Chapter02.TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop.

8. Local integrability. For every j, G_j is integrable on Q_j and v = G_j a.e. on Q_j (step 6), so v is integrable on Q_j (Integrable.congr). Every compact K ⊆ U lies in some Q_j (1(e)), so v is integrable on K. Since U is open, hence locally closed (hU.isLocallyClosed), and ℝⁿ is locally compact, locallyIntegrableOn_iff gives LocallyIntegrableOn v U volume.

9. ψ is strictly increasing (step 4); together with steps 7 and 8 this proves the claim. ∎

## Key steps

1. Compact exhaustion Q_j = {x ∈ closedBall(0, j+1) : 1/(j+1) ≤ infEDist(x, Uᶜ)}: compact, ⊆ U, Q_j ⊆ interior Q_{j+1}, and every compact K ⊆ U lies in some Q_j.
2. The finite nets make {[u_k]_{Q_j}} totally bounded in the complete space L¹(Q_j), so its closure is compact.
3. Nested convergent subsequences ψ_{j+1} = ψ_j ∘ φ_{j+1} and the diagonal ψ(k) = ψ_k(k) (strictly increasing) converge in every L¹(Q_j) (or: Tychonoff on ∏_j closure S_j).
4. Limits G_j agree a.e. on the smaller Q_i; glue v := G_{j(x)}(x) with j(x) the least j with x ∈ Q_j, v = 0 off U; v = G_j a.e. on Q_j.
5. ∫⁻_K‖u_{ψ(k)} − v‖ₑ ≤ ∫⁻_{Q_j}‖u_{ψ(k)} − v‖ₑ → 0 for compact K ⊆ Q_j; v integrable on each Q_j, so LocallyIntegrableOn v U.

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json (mode local-project; project 1b1689a8deba89d58b36b1a04dba493693824437; mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch02/{Contract.lean,README.md} against the workspace copies (identical)`
- `grep -n 'BV|IsLocallyBV|bvVariation|TendstoLocallyInL1On|IsRelativelyCompactIn' GMT/Ch02/Contract.lean (BVCompactness at lines 240-252)`
- `grep -n 'theorem|lemma|def' simongmt/Poincare/SimonGMT/Chapter02/BV.lean, then a full read`
- `grep -n '2.6|BVCompactness|open W' GMT/Ch02/README.md (row 7; erratum line 87); sed -n 540,630p book/sources/chapter-02-source.txt (printed 2.5-2.6)`
- `grep -n 'theorem|lemma|instance|def ' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -n 'exists_cthickening_subset_open|IsCompact.cthickening|closure_thickening_subset_cthickening|bounded_above_of_compact_support|ContDiff.lipschitzWith_of_hasCompactSupport|integral_norm_eq_lintegral_enorm|convolution_lsmul_swap|toReal_le_of_le_ofReal' mathlib/Mathlib`
- `grep -rlE 'Kolmogorov.?Riesz|Rellich|Frechet.?Kolmogorov|BoundedVariation.*compact|TotallyBounded.*Lp ' mathlib/Mathlib/{MeasureTheory,Analysis,Topology}; grep -rln mollif mathlib/Mathlib`
- `lean #check batches (Names, Names2, Names3, Sig, Sig2, Sig3, Sig4 .lean) for every lemma cited in the child proofs, e.g. IsOpen.measure_pos, lintegral_add_right, setLIntegral_const, ENNReal.le_div_iff_mul_le, Real.mul_iSup_of_nonneg, fderiv_const_smul, integral_const_mul, Integrable.bdd_mul, norm_integral_le_of_norm_le, finite_cover_balls_of_compact, abs_sub_round, lintegral_add_left', ContinuousOn.aestronglyMeasurable, TotallyBounded.isCompact_of_isClosed, IsCompact.tendsto_subseq, Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm, locallyIntegrableOn_iff, Metric.infEDist, Metric.finite_approx_of_totallyBounded; #synth FirstCountableTopology ((j : ℕ) → Lp ℝ 1 (volume.restrict (Q j)))`
- `python3 -I gen_checks.py (verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement), then lean NodeChallenge_00..04.lean against a scratch olean of GMT.Ch02.Submission`
- `python3 -I final_checks.py (AssemblyFinal.lean built from dag.json's lean_statement for root.bv_results-a1.mollifier_estimate-a1 plus the 5 child statements; lean_name scan over dag.json, nodes/*/decomposition-v*.json and every run file), then lean final/AssemblyFinal.lean`
- `lean checks_v1/Truth12.lean, checks_v1/Truth3.lean, prove4/Child4.lean, prove5/Child5.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/EMetricSpace/BoundedVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-compactness-a1/parent-child-handoff.json`
- `/tmp/bvcpt-decomp-tCL0IZ/final/AssemblyFinal.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/final/NodeChallenge_00.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/checks_v1/Truth12.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/checks_v1/Truth3.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/prove4/Child4.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/prove5/Child5.lean`

Contract: the snapshot Contract.lean and README.md are byte-identical to the workspace copies. BVCompactness is the frozen proposition targeted here, and README row 7 / erratum line 87 fix the open-W reading.

SimonGMT: BV.lean supplies the definitions and the A3/A4 library steps: ofReal_integral_le_bvVariationOn, IsC1TestField.isLipschitzTestField, bvVariationOn_le_liminf_of_locallyL1 and isLocallyBV_of_locallyL1_of_uniform_bound. It does not supply subsequence extraction, which README row 7 marks as new.

Mathlib supplies the analytic API: convolution_lsmul_swap, ContDiffBump.normed (needs an extra import of BumpFunction.Normed), the thickening lemmas, Lp completeness, totally bounded ⇒ compact closure, IsCompact.tendsto_subseq, the countable-product FirstCountableTopology instance, finite_cover_balls_of_compact and round/abs_sub_round. It has no L¹ compactness theorem (no Kolmogorov–Riesz/Rellich match; its BoundedVariation file is 1-D eVariationOn) and no mollifier lemma. So children 3–5 are genuine new obligations, and children 1–2 are new SimonGMT-specific lemmas.

Checks:
- All 5 lean_statements validate, and their comparator-generated NodeChallenge modules compile.
- The generated assembly proves BVCompactness from the uncle type and the 5 child types, with axioms [propext, Classical.choice, Quot.sound].
- All 5 children are proved outright in Lean with the same axioms.
- None of the 5 names collides with a reserved declaration.
