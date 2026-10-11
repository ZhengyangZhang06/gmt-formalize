# Parent-supplied natural-language proof

- Parent DAG node: `root.radon_compactness-a1`
- Child DAG node: `root.radon_compactness-a1.rc_diagonal_subseq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `rc_diagonal_subseq`.
Source: the parent proof of Simon Thm 4.16 (corrected), Step 4: “By Bolzano–Weierstrass choose successively infinite sets ℕ ⊇ N_1 ⊇ N_2 ⊇ ⋯ such that (F_{j_p,k}(g_p))_{k∈N_p} converges, and let φ(k) be the k-th element of N_k … Then φ is strictly increasing … and (φ(k))_{k≥p} is a sequence in N_p”. Here it is written with strictly increasing maps (N_p = ψ_p(ℕ)) for an abstract countable family of bounded sequences.

Standard facts used:
- (a) A strictly increasing σ : ℕ → ℕ satisfies σ(n) ≥ n for every n (induction: σ(0) ≥ 0 and σ(n+1) > σ(n) ≥ n).
- (b) A composition of strictly increasing maps ℕ → ℕ is strictly increasing.
- (c) If x_n → L in ℝ and τ : ℕ → ℕ is strictly increasing, then x_{τ(n)} → L.
- (d) Bolzano–Weierstrass: every bounded real sequence has a convergent subsequence.

1. Trivial case and enumeration. If ι is empty, φ := id is strictly increasing and the convergence claim is vacuous. Otherwise ι is countable and nonempty, so there is a surjection e : ℕ → ι. For p ∈ ℕ put b_p(k) := a_k(e(p)). By hypothesis |b_p(k)| ≤ C_{e(p)} for all k.
2. Successive subsequences.
   - By (d), choose a strictly increasing σ_0 with (b_0(σ_0(m)))_m convergent, and put ψ_0 := σ_0.
   - Given a strictly increasing ψ_{p−1} (p ≥ 1), the sequence (b_p(ψ_{p−1}(m)))_m is bounded by C_{e(p)}. By (d) there is a strictly increasing σ_p with (b_p(ψ_{p−1}(σ_p(m))))_m convergent. Put ψ_p := ψ_{p−1} ∘ σ_p, which is strictly increasing by (b).
   - By recursion this gives strictly increasing ψ_0, ψ_1, … with ψ_p = ψ_{p−1} ∘ σ_p, and limits L_p := lim_m b_p(ψ_p(m)) for every p. In the parent's notation, N_p := ψ_p(ℕ) is a decreasing sequence of infinite sets along which b_p converges.
3. The diagonal map is strictly increasing. Define φ(m) := ψ_m(m). Then φ(m+1) = ψ_m(σ_{m+1}(m+1)) ≥ ψ_m(m+1) > ψ_m(m) = φ(m). This uses σ_{m+1}(m+1) ≥ m+1 by (a), and that ψ_m is strictly increasing (in particular monotone).
4. Each b_p converges along φ. Fix p.
   - For m ≥ p let ρ_m := σ_{p+1} ∘ ⋯ ∘ σ_m (with ρ_p := id). It is strictly increasing by (b), and ψ_m = ψ_p ∘ ρ_m.
   - Put τ(m) := ρ_m(m) for m ≥ p. Then φ(m) = ψ_p(τ(m)).
   - Since ρ_{m+1} = ρ_m ∘ σ_{m+1}, we get τ(m+1) = ρ_m(σ_{m+1}(m+1)) ≥ ρ_m(m+1) > ρ_m(m) = τ(m), by (a) and strict monotonicity of ρ_m.
   - Hence (b_p(φ(p+n)))_{n∈ℕ} = (b_p(ψ_p(τ(p+n))))_n is a subsequence of the convergent sequence (b_p(ψ_p(n)))_n, so it converges to L_p by (c).
   - Dropping the finitely many terms with index < p does not affect convergence, so b_p(φ(m)) → L_p as m → ∞.
5. Conclusion. Let i ∈ ι and choose p with e(p) = i. Then a_{φ(m)}(i) = b_p(φ(m)) → L_p. So φ is strictly increasing and (a_{φ(k)}(i))_k converges for every i ∈ ι. ∎

Formalization note (non-binding; elaborated in a scratch check, standard axioms only). The same conclusion is the sequential compactness of a countable product of compact intervals.
- With C_i from the hypothesis, every a_k lies in the compact set `Set.pi univ (fun i => Icc (-C i) (C i))` ⊆ ι → ℝ (`isCompact_univ_pi`, `abs_le`).
- ι → ℝ is first countable for countable ι (Topology/Bases.lean:781).
- `IsCompact.tendsto_subseq` (Topology/Sequences.lean:298) then yields φ and b with a ∘ φ → b.
- `((continuous_apply i).tendsto b).comp` gives the coordinatewise limits.

## Key steps

1. Empty ι is trivial; otherwise enumerate ι by a surjection e : ℕ → ι and set b_p(k) = a_k(e(p)).
2. Recursively choose strictly increasing ψ_p = ψ_{p−1} ∘ σ_p with b_p ∘ ψ_p convergent (Bolzano–Weierstrass).
3. The diagonal φ(m) = ψ_m(m) is strictly increasing because σ_{m+1}(m+1) ≥ m+1.
4. For m ≥ p, φ(m) = ψ_p(τ(m)) with τ strictly increasing, so b_p ∘ φ converges.
5. Every i equals some e(p), so a_{φ(k)}(i) converges.

## Reference use

### local-project

Queries:
- `cat manifest.json (snapshot root e8e26216f05cbb4e)`
- `rg -n '^def RadonCompactness|^def RieszPositive|^noncomputable abbrev caratheodoryMeasure|^universe|^open|^namespace' project/GMT/Ch01/Contract.lean`
- `cmp project/GMT/Ch01/Contract.lean project/GMT/Ch01/Submission.lean`
- `rg -n '4.16|RadonCompactness' project/GMT/Ch01/README.md`
- `rg -n 'theorem integral_rieszMeasure|noncomputable def rieszMeasure|instance regular_rieszMeasure' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`
- `rg -n 'def nnrealPart|def toReal |lemma nnrealPart_sub_nnrealPart_neg|def toNNRealLinear|lemma toNNRealLinear_apply|instance partialOrder' mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `rg -n 'def mk₀' mathlib/Mathlib/Algebra/Order/Module/PositiveLinearMap.lean`
- `rg -n 'theorem Continuous.integrable_of_hasCompactSupport' mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `rg -n 'theorem norm_setIntegral_le_of_norm_le_const ' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `rg -n 'instance instSeparableSpace|instance instSecondCountableTopology' mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `rg -n 'theorem IsSeparable.exists_countable_dense_subset' mathlib/Mathlib/Topology/Metrizable/Basic.lean; rg -n 'theorem IsSeparable.of_separableSpace' mathlib/Mathlib/Topology/Bases.lean`
- `rg -n 'theorem dist_apply_le_dist' mathlib/Mathlib/Topology/ContinuousMap/Compact.lean`
- `rg -n 'sigmaCompactSpace_of_locallyCompact_secondCountable|noncomputable def choice|theorem exists_superset_of_isCompact|theorem subset_interior_succ' mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `rg -n 'theorem IsCompact.tendsto_subseq ' mathlib/Mathlib/Topology/Sequences.lean; rg -n -F 'FirstCountableTopology (∀ i, X i)' mathlib/Mathlib/Topology/Bases.lean; rg -n 'theorem isCompact_univ_pi' mathlib/Mathlib/Topology/`
- `rg -n 'WeaklyLocallyCompactSpace.locallyCompactSpace' mathlib/Mathlib/Topology/Separation/Basic.lean`
- `rg -n 'theorem subalgebra_topologicalClosure_eq_top_of_separatesPoints' mathlib/Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean`
- `rg -n -i vague mathlib/Mathlib/MeasureTheory (no match, exit 1)`
- `rg -n 'SeparableSpace C_c' plus a C_c-SeparableSpace regex over mathlib/Mathlib (no match, exit 1)`
- `rg -n 'theorem .*diagonal.*subseq|theorem .*subseq.*countable|tendsto_subseq_of_bounded' mathlib/Mathlib`
- `rg -n 'SecondCountableSpace' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/ project/GMT/Ch01/Contract.lean (no match, exit 1)`
- `cmp -s of 14 cited snapshot Mathlib files against lake-packages-25730c7c/mathlib (all identical)`
- `rg -n 'theorem .*[Ii]ntegrable|StrictMono|SeparableSpace|IsSeparable|nnrealPart|→ₚ' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01 (pinned simongmt, outside the snapshot)`
- `python3 -I scan of lean_name in dag.json and nodes/*/decomposition-v1.json for the six rc_ names (no collision)`
- `lake env lean on a scratch file outside the repo: contract text minus main_theorem plus the six frozen statements (contract imports only); then with import Mathlib.Topology.ContinuousMap.SecondCountableSpace, full child proofs, parent assembly, comparator-shaped targets and #print axioms`
- `sed -n 1745,1778p book/chapter-01.txt (printed Theorem 4.16 and its proof)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Algebra/Order/Module/PositiveLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/ContinuousMap/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Separation/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/MetricSpace/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Radon.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/dag.json`

SNAPSHOT AND CONTRACT. The manifest pins project ec1c322 and Mathlib 25730c7c. The snapshot Contract.lean is byte-identical to Submission.lean. It defines RieszPositive (l. 267) and RadonCompactness (l. 303) in namespace GMT.Ch01, with `universe u v` (l. 69) and the opens at ll. 63–65. README row 15 marks the corrected 4.16 as New for non-compact X.

NO LIBRARY SHORTCUT.
- No 'vague' match in Mathlib MeasureTheory and no C_c separability statement.
- For subsequence extraction there is only the single-sequence Bolzano–Weierstrass tendsto_subseq_of_bounded (Topology/MetricSpace/Sequences.lean:38).
- The pinned simongmt Chapter01 (outside the snapshot) has:
  - finiteMeasure_tendsto_subseq_of_compact_metrizable and simon_theorem_4_16_compact_metrizable (compact X only);
  - the bridges IsRadonOuterMeasure.toCaratheodoryMeasure_apply_all, isRadonOuterMeasure_toOuterMeasure and integral_radonCaratheodoryMeasure;
  - a real-RMK wrapper in Radon.lean;
  - no C_c-integrability, diagonal-subsequence or C_c-separability lemma.

THE SNAPSHOT HAS EVERYTHING THE SIX CHILDREN NEED.
- RealRMK.rieszMeasure, integral_rieszMeasure and regular_rieszMeasure: Real.lean:65,345,357; NNRealRMK.integral_rieszMeasure: NNReal.lean:47.
- CompactlySupported.lean: the pointwise partialOrder (444), nnrealPart (688), toReal (739), nnrealPart_sub_nnrealPart_neg (749), toNNRealLinear and toNNRealLinear_apply (775, 782).
- PositiveLinearMap.mk₀ (PositiveLinearMap.lean:206).
- Continuous.integrable_of_hasCompactSupport (LocallyIntegrable.lean:622) and norm_setIntegral_le_of_norm_le_const (Bochner/Set.lean:613).
- ContinuousMap.instSeparableSpace (SecondCountableSpace.lean:108). This module is NOT in the contract's import closure: no match in the RMK files or Contract.lean, and #check fails in the contract scope. Stone–Weierstrass subalgebra_topologicalClosure_eq_top_of_separatesPoints (StoneWeierstrass.lean:264) is in the closure.
- Separability and metrics: IsSeparable.exists_countable_dense_subset (Metrizable/Basic.lean:185), IsSeparable.of_separableSpace (Bases.lean:599), ContinuousMap.dist_apply_le_dist (ContinuousMap/Compact.lean:114).
- Exhaustions: sigmaCompactSpace_of_locallyCompact_secondCountable (SigmaCompact.lean:187), CompactExhaustion.choice (418), exists_superset_of_isCompact (376).
- Subsequences: IsCompact.tendsto_subseq (Sequences.lean:298), countable-pi first countability (Bases.lean:781), isCompact_univ_pi (Compactness/Compact.lean:1172).
- WeaklyLocallyCompactSpace.locallyCompactSpace (Separation/Basic.lean:1196).
The 14 cmp-checked snapshot Mathlib files equal the build packages.

SCRATCH CHECK (outside the repo, deleted afterwards).
- The six frozen statements elaborate with the contract imports.
- All six children were proved, with only propext, Classical.choice and Quot.sound.
- RadonCompactness was proved from the six children with Submission.riesz_positive stubbed.
- Comparator-shaped `exact Submission.X` targets were accepted.

COMPARATOR. gmt-compare.py elaborates child statements in the replayed contract scope (namespace GMT.Ch01, opens, `universe u v`). It byte-freezes only Contract.lean and the Lake inputs, so a candidate may add a Mathlib import.

SOURCE TEXT. chapter-01.txt ll. 1750–1778 is the printed 4.16 proof, which the parent's corrected Steps 1–7 expand.
