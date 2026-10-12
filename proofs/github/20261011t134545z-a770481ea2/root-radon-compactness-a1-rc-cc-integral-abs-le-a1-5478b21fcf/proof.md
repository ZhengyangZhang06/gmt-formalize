# Parent-supplied natural-language proof

- Parent DAG node: `root.radon_compactness-a1`
- Child DAG node: `root.radon_compactness-a1.rc_cc_integral_abs_le-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `rc_cc_integral_abs_le`.
Source: the parent proof of Simon Thm 4.16 (corrected). It combines the Step 2 estimate “|F_{j,k}(g)| ≤ M_j‖g‖_∞” with Step 3 “∫_X f dμ_k = F_{j,k}(f|_{K_j}), because f = 0 off K_j”. Here it is stated for one Radon outer measure, with the compact set taken to be tsupport f itself.

Notation as in Lemma 1.6/Remark 1.7: 𝓜_μ is the σ-algebra of μ-measurable sets and μ̄ = caratheodoryMeasure μ is μ restricted to 𝓜_μ. Put S := tsupport f.

1. S ∈ 𝓜_μ and μ̄(S) = μ(S) < ∞. S is closed, hence Borel, hence μ-measurable by the Borel regularity in (R1); so μ̄(S) = μ(S). S is compact because f has compact support, so μ(S) < ∞ by (R1).
2. Reduction to S. If x ∉ S, then x is not in {f ≠ 0} (S is its closure), so f(x) = 0. Hence f = f·1_S and ∫_X f dμ̄ = ∫_S f dμ̄.
3. The estimate on S.
   - If S = ∅, then f ≡ 0 and both sides of the claim are 0 (μ(∅) = 0).
   - If S ≠ ∅, pick x ∈ S; then C ≥ |f(x)| ≥ 0. Since |f| ≤ C on S and μ̄(S) < ∞, the standard bound for integrals over a set of finite measure gives |∫_S f dμ̄| ≤ ∫_S |f| dμ̄ ≤ ∫_S C dμ̄ = C·μ̄(S).
   - The bound would hold trivially for a non-integrable integrand, whose Bochner integral is 0. Here f is in fact integrable: it is measurable, bounded on the finite-measure set S, and zero elsewhere.
4. Conclusion. |∫_X f dμ̄| = |∫_S f dμ̄| ≤ C·μ̄(S) = μ(S)·C, where μ(S) < ∞ is read as a real number. ∎

Formalization note (non-binding; elaborated in a scratch check, standard axioms only).
- Set `letI : MeasurableSpace X := μ.caratheodory` and get `OpensMeasurableSpace X` from `hμ.borel_regular.borel_le_caratheodory`.
- Rewrite the integral as a set integral over `tsupport f` using `setIntegral_eq_integral_of_forall_compl_eq_zero` with `image_eq_zero_of_notMem_tsupport`.
- Apply `norm_setIntegral_le_of_norm_le_const` (Mathlib Integral/Bochner/Set.lean:613); it needs `caratheodoryMeasure μ (tsupport f) < ∞`.
- Convert `Measure.real` using `hμ.toCaratheodoryMeasure_apply_all (tsupport f)` and `mul_comm`.

## Key steps

1. tsupport f is closed and compact, so it is μ-measurable with μ̄(tsupport f) = μ(tsupport f) < ∞.
2. f vanishes off tsupport f, so ∫_X f dμ̄ = ∫_{tsupport f} f dμ̄.
3. |∫_S f dμ̄| ≤ C·μ̄(S) when |f| ≤ C on a finite-measure set S (C ≥ 0 unless S = ∅; the case S = ∅ is trivial).

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
