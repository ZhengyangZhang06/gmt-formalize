# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.compactness-a1`
- Child DAG node: `root.bv_results-a1.compactness-a1.finite_net-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2, Theorem 2.6 (p. 50). The printed proof reduces compactness to precompactness in L¹_loc(U), proved “involving mollification and Arzela's theorem” [GT01, Thm 7.22]; this step is the Arzelà-type finite-net argument. The argument below is step A1(iii)–(iv) of the reviewed proof supplied to node root.bv_results-a1.compactness-a1 (Section A of the parent root.bv_results-a1), specialized to this self-contained statement with the details filled in. Notation: ℝⁿ = Rn n = EuclideanSpace ℝ (Fin n), μ = volume (Lebesgue measure), ∫⁻ is the lower Lebesgue integral in [0,∞], ‖a‖ₑ ∈ [0,∞) the extended norm, ofReal = ENNReal.ofReal.

Statement recalled. Q ⊆ ℝⁿ is compact, every u_k is integrable on Q, and (approximation hypothesis) for every ε > 0 there are reals B, Λ and functions w_k (k ∈ ℕ) with |w_k(x)| ≤ B (x ∈ Q), |w_k(x) − w_k(y)| ≤ Λ‖x − y‖ (x, y ∈ Q) and ∫⁻_Q ‖u_k − w_k‖ₑ ≤ ofReal ε for all k. Claim: for every ε > 0 there is a finite F ⊆ ℕ such that every k has some j ∈ F with ∫⁻_Q ‖u_k − u_j‖ₑ < ofReal ε.

1. Fix ε > 0. Q is compact, hence closed, hence measurable, and μ(Q) < ∞ (IsCompact.measure_lt_top). Put m := μ(Q).toReal ≥ 0, so μ(Q) = ofReal m.

2. If Q = ∅, take F := {0}: for every k, ∫⁻_∅ ‖u_k − u_0‖ₑ = 0 < ofReal ε (μ.restrict ∅ = 0, ε > 0). Assume from now on Q ≠ ∅.

3. Apply the approximation hypothesis with ε/4 > 0 to get B, Λ and (w_k). Put Λ' := max(Λ, 0) ≥ 0; then |w_k(x) − w_k(y)| ≤ Λ‖x − y‖ ≤ Λ'‖x − y‖ for x, y ∈ Q.

4. Put η := ε / (4(m + 1)) > 0 and r := η / (3Λ' + 3) > 0. Since Q is compact there is a finite set T ⊆ Q with Q ⊆ ⋃_{q ∈ T} B(q, r) (open balls; finite_cover_balls_of_compact).

5. Rounding to a grid of spacing η/3. For k ∈ ℕ and q ∈ T let a_k(q) := round(3 w_k(q)/η) ∈ ℤ. By abs_sub_round, |3w_k(q)/η − a_k(q)| ≤ 1/2, i.e. |w_k(q) − (η/3) a_k(q)| ≤ η/6. Moreover |a_k(q)| ≤ 3|w_k(q)|/η + 1/2 ≤ 3B/η + 1 =: N, because q ∈ Q gives |w_k(q)| ≤ B. Hence every a_k lies in the set 𝒜 of functions T → {z ∈ ℤ : |z| ≤ N}, which is finite (T is finite and there are finitely many integers in [−N, N]).

6. Representatives. The set {a_k : k ∈ ℕ} ⊆ 𝒜 is finite. For each a in it choose an index j(a) ∈ ℕ with a_{j(a)} = a (for instance the least such index). Let F be the finite set {j(a) : a ∈ {a_k : k ∈ ℕ}} ⊆ ℕ (a Finset).

7. Fix k ∈ ℕ and put j := j(a_k) ∈ F, so a_j = a_k. For q ∈ T: |w_k(q) − w_j(q)| ≤ |w_k(q) − (η/3)a_k(q)| + |(η/3)a_j(q) − w_j(q)| ≤ η/6 + η/6 = η/3.

8. Let x ∈ Q and choose q ∈ T with ‖x − q‖ < r (step 4). Since x, q ∈ Q,
   |w_k(x) − w_j(x)| ≤ |w_k(x) − w_k(q)| + |w_k(q) − w_j(q)| + |w_j(q) − w_j(x)| ≤ Λ'r + η/3 + Λ'r = 2Λ'η/(3Λ' + 3) + η/3 < 2η/3 + η/3 = η,
   because 2Λ'/(3Λ' + 3) < 2/3 (equivalently 6Λ' < 6Λ' + 6). So ‖w_k(x) − w_j(x)‖ₑ ≤ ofReal η for all x ∈ Q.

9. Integrating over Q (setLIntegral_mono / ae_restrict_of_forall_mem, Q measurable): ∫⁻_Q ‖w_k − w_j‖ₑ ≤ ∫⁻_Q ofReal η = ofReal η · μ(Q) = ofReal(η m) ≤ ofReal(ε/4), since η m = ε m / (4(m + 1)) ≤ ε/4.

10. Measurability. u_k and u_j are a.e.-strongly measurable for μ.restrict Q (they are integrable on Q). Each w_i is Lipschitz on Q (step 3), hence continuous on Q, hence a.e.-strongly measurable for μ.restrict Q (ContinuousOn.aestronglyMeasurable, Q measurable). Therefore x ↦ ‖u_k(x) − w_k(x)‖ₑ and x ↦ ‖w_k(x) − w_j(x)‖ₑ are a.e.-measurable for μ.restrict Q.

11. Triangle inequality. For every x, ‖u_k(x) − u_j(x)‖ₑ ≤ ‖u_k(x) − w_k(x)‖ₑ + ‖w_k(x) − w_j(x)‖ₑ + ‖w_j(x) − u_j(x)‖ₑ (write u_k − u_j = (u_k − w_k) + (w_k − w_j) + (w_j − u_j) and apply enorm_add_le twice; equivalently edist_triangle twice). By monotonicity of ∫⁻, additivity when the left summand is a.e.-measurable (lintegral_add_left', twice, using step 10), ‖w_j − u_j‖ₑ = ‖u_j − w_j‖ₑ, the approximation hypothesis (for k and for j) and step 9:
   ∫⁻_Q ‖u_k − u_j‖ₑ ≤ ofReal(ε/4) + ofReal(ε/4) + ofReal(ε/4) = ofReal(3ε/4) < ofReal ε (as ε > 0).

12. Since k was arbitrary and j ∈ F, the finite set F has the required property. ∎

Remark (equivalent shortcut for steps 5–8, convenient in Lean). Instead of rounding, view p_k := (w_k(q))_{q ∈ T} as a point of the finite-dimensional space T → ℝ with the sup norm. All p_k lie in the closed ball of radius max(B, 0), which is compact, so {p_k : k ∈ ℕ} is totally bounded and has a finite η/2-net consisting of points of the set (Metric.finite_approx_of_totallyBounded); choosing one index j for each net point (e.g. Function.invFun) gives F with ‖p_k − p_j‖ < η/2 for some j ∈ F. Taking r := η/(4(Λ' + 1)) in step 4, step 8 becomes |w_k(x) − w_j(x)| ≤ 2Λ'r + η/2 = Λ'η/(2(Λ' + 1)) + η/2 < η, and steps 9–12 are unchanged.

## Key steps

1. Q = ∅ is trivial (F = {0}); otherwise approximate at accuracy ε/4 with B, Λ' = max(Λ,0), w_k.
2. η := ε/(4(Lⁿ(Q).toReal + 1)); finite r-net T ⊆ Q of the compact Q with r := η/(3Λ' + 3).
3. Round w_k(q), q ∈ T, to the grid (η/3)ℤ: the codes a_k : T → [−N, N] ∩ ℤ take finitely many values; F := one index per code.
4. Equal codes give |w_k − w_j| ≤ η/3 on T and |w_k − w_j| < η on Q, so ∫⁻_Q‖w_k − w_j‖ₑ ≤ ofReal(ε/4).
5. Triangle inequality with a.e.-measurable summands: ∫⁻_Q‖u_k − u_j‖ₑ ≤ ofReal(3ε/4) < ofReal ε.

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
