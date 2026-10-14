# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.lipschitz_range_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k) with Euclidean norm |·|. Lⁿ := volume on ℝⁿ. Hⁿ := μHE[n], Mathlib's Euclidean-normalised n-dimensional Hausdorff measure, which is used on ℝ^P and on ℝⁿ. On ℝⁿ itself Hⁿ = Lⁿ (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). In [0, ∞] we use the convention 0⁻¹ = ∞. For a map H : ℝⁿ → ℝ^P, H(ℝⁿ) = range H.

Source. This is step 4 of the parent proof (slicing_im_tg_c1_chart_cover) for a single Lipschitz map F = F_j, together with fact (N) of the parent proof.
- In Simon's printed proof (Ch. 3, Lemma 1.2) it is displays (1)–(2): F_j(ℝⁿ) ⊂ E_j ∪ (∪_i G_ij(ℝⁿ)) with E_j = F_j(Z_j) and Hⁿ(E_j) = 0. The printed "graph F_j" in (1) is to be read as F_j(ℝⁿ).
- The C¹ maps come from the sibling c1_approximation_eucl (Submission.lpf_c1_approximation_eucl), the vector-valued C¹ Approximation Theorem (Simon Ch. 2, 1.5; steps 2–3 of the parent proof). It says: for every K-Lipschitz u : ℝⁿ → ℝ^Q and every ε ∈ (0, ∞] there are a closed A ⊆ ℝⁿ with Lⁿ(ℝⁿ ∖ A) < ε and a C¹ map G : ℝⁿ → ℝ^Q such that u(x) = G(x) for every x ∈ A. (It also gives HasFDerivAt u (fderiv ℝ G x) x on A, which is not needed here.)

1. (C¹ approximations.) For i ∈ ℕ put ε_i := i⁻¹ ∈ (0, ∞], so ε_0 = ∞ and ε_i = 1/i for i ≥ 1. Each ε_i is positive because the natural number i is not ∞ in [0, ∞] (ENNReal.inv_pos, ENNReal.natCast_ne_top). For each i, apply c1_approximation_eucl with Q := P, u := F, the constant K and ε := ε_i. Choosing these data for all i at once (choice), we get closed sets A_i ⊆ ℝⁿ and C¹ maps G_i : ℝⁿ → ℝ^P with:
 (a) Lⁿ(ℝⁿ ∖ A_i) < ε_i;
 (b) F(x) = G_i(x) for every x ∈ A_i.
These G_i are the required C¹ maps. It remains to show Hⁿ(F(ℝⁿ) ∖ ⋃_i G_i(ℝⁿ)) = 0.

2. (The exceptional parameters form an Lⁿ-null set.) Put Z := ⋂_i (ℝⁿ ∖ A_i) = ℝⁿ ∖ ⋃_i A_i. For every i, Z ⊆ ℝⁿ ∖ A_i, so monotonicity and 1(a) give Lⁿ(Z) ≤ Lⁿ(ℝⁿ ∖ A_i) < ε_i = i⁻¹. Since i⁻¹ → 0 in [0, ∞] as i → ∞ (ENNReal.tendsto_inv_nat_nhds_zero), passing to the limit gives Lⁿ(Z) ≤ 0, i.e. Lⁿ(Z) = 0.

3. (The image of Z is Hⁿ-null; fact (N).) F is K-Lipschitz on ℝⁿ, in particular on Z.
- SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn says: if f is K-Lipschitz on a set A, then μHE[n](f(A)) ≤ K^n · μHE[n](A).
- Hence Hⁿ(F(Z)) ≤ K^n · Hⁿ(Z), where Hⁿ(Z) is computed on ℝⁿ.
- Since Hⁿ = Lⁿ on ℝⁿ, step 2 gives Hⁿ(Z) = Lⁿ(Z) = 0.
- Therefore Hⁿ(F(Z)) ≤ K^n · 0 = 0, i.e. Hⁿ(F(Z)) = 0.

4. (The uncovered part of F(ℝⁿ) lies in F(Z).) Let y ∈ F(ℝⁿ) ∖ ⋃_i G_i(ℝⁿ) and write y = F(w) with w ∈ ℝⁿ. Suppose w ∈ A_i for some i. Then 1(b) gives y = F(w) = G_i(w) ∈ G_i(ℝⁿ), contradicting y ∉ ⋃_i G_i(ℝⁿ). Hence w ∉ A_i for every i, i.e. w ∈ Z, and y = F(w) ∈ F(Z). Thus F(ℝⁿ) ∖ ⋃_i G_i(ℝⁿ) ⊆ F(Z).

5. (Conclusion.) Step 4, monotonicity of Hⁿ and step 3 give Hⁿ(F(ℝⁿ) ∖ ⋃_i G_i(ℝⁿ)) ≤ Hⁿ(F(Z)) = 0. Together with step 1 (every G_i is C¹) this proves the statement. No case distinction on n or P is needed: for n = 0 or P = 0 the same argument applies verbatim. ∎

Implementation notes.
- No new import is needed. SimonGMT Chapter02.Lipschitz, which contains euclideanHausdorffMeasure_image_le_of_lipschitzOn, is already in the frozen import closure: Poincare.SimonGMT.Chapter03.Rectifiable imports it publicly.
- Reference Lean proof: kernel-checked in an isolated scratch build importing only the frozen GMT.Ch06.Submission, in the comparator's contract scope, placed after the contract's `end` inside namespace GMT.Ch06. The sibling Submission.lpf_c1_approximation_eucl must be present. With the sibling's accepted proof, `#print axioms` shows only propext, Classical.choice and Quot.sound.

theorem Submission.slicing_im_tg_cc_lipschitz_range_c1_cover : ∀ (n P : ℕ) (F : Eucl n → Eucl P) (K : ℝ≥0), LipschitzWith K F → ∃ G : ℕ → Eucl n → Eucl P, (∀ i, ContDiff ℝ 1 (G i)) ∧ (μHE[n] : Measure (Eucl P)) (range F \ ⋃ i, range (G i)) = 0 := by
  intro n P F K hF
  -- ε_i := i⁻¹ ∈ (0, ∞] (ε_0 = ∞)
  have hε : ∀ i : ℕ, (0 : ℝ≥0∞) < (i : ℝ≥0∞)⁻¹ := fun i =>
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i)
  -- step 1: closed A_i, C¹ G_i with F = G_i on A_i and Lⁿ(A_iᶜ) < i⁻¹
  choose A G hAc hAm hG hAG using fun i : ℕ =>
    Submission.lpf_c1_approximation_eucl n P F K hF _ (hε i)
  refine ⟨G, hG, ?_⟩
  -- step 2: Z := ⋂_i A_iᶜ is Lⁿ-null
  set Z : Set (Eucl n) := ⋂ i, (A i)ᶜ with hZdef
  have hZ : (volume : Measure (Eucl n)) Z = 0 := by
    refine le_antisymm ?_ bot_le
    refine ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun i => ?_
    exact (measure_mono (iInter_subset _ i)).trans (hAm i).le
  -- step 3: F(Z) is Hⁿ-null
  have hFZ : (μHE[n] : Measure (Eucl P)) (F '' Z) = 0 := by
    refine le_antisymm ?_ bot_le
    calc (μHE[n] : Measure (Eucl P)) (F '' Z)
        ≤ (K : ℝ≥0∞) ^ n * (μHE[n] : Measure (Eucl n)) Z :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            hF.lipschitzOnWith
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ, mul_zero]
  -- steps 4–5: F(ℝⁿ) ∖ ⋃_i G_i(ℝⁿ) ⊆ F(Z)
  refine measure_mono_null ?_ hFZ
  rintro y ⟨⟨w, rfl⟩, hy⟩
  refine ⟨w, ?_, rfl⟩
  rw [hZdef, mem_iInter]
  intro i hwi
  exact hy (mem_iUnion.2 ⟨i, w, ((hAG i w hwi).1).symm⟩)

## Key steps

1. Apply c1_approximation_eucl (Submission.lpf_c1_approximation_eucl) to F with ε_i := i⁻¹ ∈ (0, ∞] (i ∈ ℕ). This gives closed A_i with Lⁿ(ℝⁿ ∖ A_i) < i⁻¹ and C¹ maps G_i with F = G_i on A_i.
2. Z := ⋂_i (ℝⁿ ∖ A_i) has Lⁿ(Z) ≤ i⁻¹ for all i, so Lⁿ(Z) = 0 (ENNReal.tendsto_inv_nat_nhds_zero).
3. The Lipschitz image bound (SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn) and μHE[n] = volume on ℝⁿ give Hⁿ(F(Z)) ≤ K^n · Lⁿ(Z) = 0.
4. If y = F(w) ∉ ⋃_i G_i(ℝⁿ), then w ∉ A_i for every i (else y = G_i(w)), so w ∈ Z. Hence F(ℝⁿ) ∖ ⋃_i G_i(ℝⁿ) ⊆ F(Z).
5. By monotonicity, Hⁿ(F(ℝⁿ) ∖ ⋃_i G_i(ℝⁿ)) ≤ Hⁿ(F(Z)) = 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Contract.lean (identical); git show fe5ecf7a:GMT/Ch06/Submission.lean = frozen contract (this node's proof base has no lemmas)`
- `rg -n 'theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem exists_countable_basis|theorem Countable.exists_eq_range|tendsto_inv_nat_nhds_zero|theorem finrank_euclideanSpace_fin|theorem lipschitzOnWith_empty|def eqv' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'ContDiff.locallyLipschitz' local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus; rg -n 'theorem measure_mono_null|theorem measure_union_null' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -c 'slicing_im_tg_cc|lipschitz_range_c1_cover|contDiff_range_chart_cover' local-references/197bdd4b88278494 (exit 1: no match)`
- `grep -n 'def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; grep -n 'import' Chapter03/Rectifiable.lean (public import Poincare.SimonGMT.Chapter02.Lipschitz)`
- `grep -n 'theorem area_image_eq_zero_of_critical|theorem area_image_criticalSet_eq_zero' simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean; grep -n 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' Chapter02/Lipschitz.lean`
- `ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 (AreaCritical.olean, Lipschitz.olean, AreaLipschitz.olean, AreaDomain.olean present)`
- `python3 over dag.json (467 nodes): status/type/candidate of lpf_c1_approximation_eucl, lpf_c1_local_antilipschitz, lpf_c1_approximation_real, lpf_countably_rectifiable_c1_cover, lpf_lipschitz_c1_immersion_pieces, slicing_im_coarea_chart_cover; new-name uniqueness; no node with either new type; cross-branch reuse precedents and their parents' statuses`
- `read nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json, nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/decomposition-v1.json (reuse-child conventions)`
- `json fields proof/key_steps of nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-9651ace1ab/parent-supplied-natural-proof.json and ...-c1-fa0007faad/parent-supplied-natural-proof.json (copied verbatim)`
- `git show eff6bc80:GMT/Ch06/Submission.lean and 961fc108:GMT/Ch06/Submission.lean (accepted Lean code; frozen types byte-equal to dag.json); survey of extra imports in accepted candidates (AreaDomain x6, AreaBranches, DensityComparison, RadonPolarRepresentation, RadonCaratheodoryIntegral)`
- `python3 -I verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem'); python3 -I verifier/lean_contract.py validate_lean_statement on all 5 types (OK)`
- `lean Scratch/{Stmts,Assembly,Imports,OnlyE,OnlyE_noimport,OnlyD,OnlyParent,Full,FullTargets,Final}.lean in /tmp/cc_split_Zpx7V0 (LEAN_PATH to shared prebuilt oleans; frozen Submission.olean rebuilt in scratch)`
- `sed -n 1,80p book/chapter-03.txt (Simon Ch. 3, 1.1, Lemma 1.2 printed proof, Remark 1.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-1b3924ced5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-1b3924ced5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-9651ace1ab/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-fa0007faad/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/cc_split_Zpx7V0/Scratch/Stmts.lean`
- `/tmp/cc_split_Zpx7V0/Scratch/Final.lean`
- `/tmp/cc_split_Zpx7V0/Scratch/OnlyE_noimport.lean`
- `/tmp/cc_split_Zpx7V0/Scratch/OnlyD.lean`
- `/tmp/cc_split_Zpx7V0/Scratch/OnlyParent.lean`

Snapshot and base:
- The snapshot (project d8d46c95, Mathlib 25730c7c) Contract.lean is byte-identical to the workspace contract.
- This node's proof base fe5ecf7a has Submission.lean = the frozen contract, so accepted lemmas from other branches are usable only as reuse children.

Library facts used by the new children (all verified):
- Mathlib (snapshot paths above):
 - μHE[d] = volume on ℝ^d: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Geometry/Euclidean/Volume/Measure.lean:187;
 - ContDiff.locallyLipschitz, Analysis/Calculus/ContDiff/RCLike.lean:143;
 - TopologicalSpace.exists_countable_basis, Topology/Bases.lean:810;
 - Set.Countable.exists_eq_range, Data/Set/Countable.lean:149;
 - ENNReal.tendsto_inv_nat_nhds_zero, Topology/Instances/ENNReal/Lemmas.lean:486;
 - finrank_euclideanSpace_fin, Analysis/InnerProductSpace/PiL2.lean:205;
 - lipschitzOnWith_empty, measure_mono_null, measure_union_null and Denumerable.eqv.
- SimonGMT:
 - CountablyRectifiable is ∃ M₀, μHE[n] M₀ = 0 ∧ ∃ F, (∀ j, ∃ K, LipschitzWith K (F j)) ∧ M ⊆ M₀ ∪ ⋃ j, range (F j) (Chapter03/Rectifiable.lean:34);
 - Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216; already in the frozen import closure via Chapter03.Rectifiable);
 - Chapter02.area_image_criticalSet_eq_zero (Chapter02/AreaCritical.lean:185; no hypotheses on f; AreaCritical.olean is prebuilt).
 Both SimonGMT lemmas depend only on propext, Classical.choice and Quot.sound.

Reuse:
- lpf_c1_approximation_eucl (eff6bc80) and lpf_c1_local_antilipschitz (961fc108) are accepted. Their frozen types are byte-identical to dag.json and to the accepted Lean code.
- The identical-type twin lpf_countably_rectifiable_c1_cover is only speculative-ready, and the coarea twin is decomposing, so neither is reused.
- The new names slicing_im_tg_cc_lipschitz_range_c1_cover and slicing_im_tg_cc_contDiff_range_chart_cover have no match in the snapshot (rg exit 1), in SimonGMT, or among the 467 DAG nodes.

Kernel checks:
- All 5 types pass validate_lean_statement and elaborate in the exact comparator scope.
- Final.lean (real accepted proofs + new children + assembly + `exact Submission.X` targets) compiles cleanly, and every target depends only on propext, Classical.choice and Quot.sound.
