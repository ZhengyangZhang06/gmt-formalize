# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.bf_trichotomy-a1`
- Child DAG node: `root.rectifiability-a1.bf_trichotomy-a1.witness_set_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2(d) of the parent-supplied proof of rectifiability_bf_trichotomy: T3 is σ-compact, hence Borel. The parent uses this set for the joint measurability in its Fubini step 5, and the sibling slice_density_null uses it for the Borel sets D_{j,w} of step 3(c).

1. Since E is σ-compact, E = ⋃_{n∈ℕ} K_n with each K_n compact. In Lean, IsSigmaCompact E unfolds to ∃ K : ℕ → Set (Eucl N), (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = E.

2. For n, l ∈ ℕ, let C_{n,l} be the set of (x,(a,v)) ∈ ℝ^N × (ℝ^N × (ℝ^N)^k) with
 - x ∈ K_n,
 - 1/(l+1) ≤ |x − a| ≤ δ − 1/(l+1),
 - ‖(a,v)‖ ≤ l,
 - L_v x = L_v a.
 Each condition is closed. K_n is closed (compact in a Hausdorff space), and the other conditions are non-strict inequalities or an equality between continuous functions of (x,a,v): norms and inner products are continuous, and ℝᵏ is Hausdorff. So C_{n,l} is closed. It is bounded, because x ranges in the bounded set K_n and (a,v) in the closed ball of radius l. The ambient space is a finite-dimensional normed space, hence proper, so C_{n,l} is compact (Metric.isCompact_of_isClosed_isBounded).

3. The projection π(x,(a,v)) := (a,v) is continuous, so π(C_{n,l}) is compact. It is therefore closed in the Hausdorff space ℝ^N × (ℝ^N)^k and measurable (IsCompact.measurableSet; this product of second-countable spaces carries its Borel σ-algebra).

4. W = ⋃_{n,l∈ℕ} π(C_{n,l}).
 - ⊇: let (x,(a,v)) ∈ C_{n,l}. Then x ∈ K_n ⊆ E. Also |x − a| ≥ 1/(l+1) > 0, so x ≠ a, and |x − a| ≤ δ − 1/(l+1) < δ. Finally L_v x = L_v a. So (a,v) ∈ W.
 - ⊆: let (a,v) ∈ W with witness x ∈ E, so x ≠ a, |x − a| < δ and L_v x = L_v a. Choose n with x ∈ K_n. Since |x − a| > 0, δ − |x − a| > 0 and ‖(a,v)‖ < ∞, the Archimedean property gives l ∈ ℕ with 1/(l+1) ≤ min(|x − a|, δ − |x − a|) and ‖(a,v)‖ ≤ l. Then (x,(a,v)) ∈ C_{n,l} and (a,v) = π(x,(a,v)).

5. So W is a countable union of measurable sets, hence measurable. Equivalently, W is σ-compact as the union of the compact sets π(C_{n,l}). ∎

Lean reference proof (appendix; written by the independent Lean reviewer of this decomposition and re-compiled by the author). It is compile-checked as a single declaration against the exact frozen statement inside `namespace GMT.Ch06` of a scratch copy of the frozen project (commit d8d46c9587747dee0751a1f780fcafdba16a3886, Lean v4.35.0-rc3, pinned Mathlib 25730c7c), with no sibling dependencies; #print axioms = [propext, Classical.choice, Quot.sound]. It introduces no auxiliary declarations.
```lean
theorem Submission.rectifiability_bf_witness_set_measurable : (∀ (N m : ℕ) (E : Set (Eucl N)) (δ : ℝ), IsSigmaCompact E → MeasurableSet {p : Eucl N × (Fin (m + 1) → Eucl N) | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))}) := by
  intro N m E δ hE
  obtain ⟨K, hK, hKE⟩ := hE
  have hLc : Continuous (fun q : Eucl N × (Eucl N × (Fin (m + 1) → Eucl N)) =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.1) : Eucl (m + 1))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).inner continuous_fst
  have hLc' : Continuous (fun q : Eucl N × (Eucl N × (Fin (m + 1) → Eucl N)) =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.2.1) : Eucl (m + 1))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).inner
      (continuous_fst.comp continuous_snd)
  let C : ℕ → ℕ → Set (Eucl N × (Eucl N × (Fin (m + 1) → Eucl N))) := fun n l =>
    (K n ×ˢ closedBall (0 : Eucl N × (Fin (m + 1) → Eucl N)) l) ∩
      ({q | 1 / ((l : ℝ) + 1) ≤ dist q.1 q.2.1} ∩ {q | dist q.1 q.2.1 ≤ δ - 1 / ((l : ℝ) + 1)} ∩
        {q | (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.1) : Eucl (m + 1)) =
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.2.1) : Eucl (m + 1))})
  have hCc : ∀ n l, IsCompact (C n l) := by
    intro n l
    refine ((hK n).prod (isCompact_closedBall _ _)).inter_right ?_
    refine ((isClosed_le continuous_const ?_).inter (isClosed_le ?_ continuous_const)).inter
      (isClosed_eq hLc hLc')
    · exact continuous_fst.dist (continuous_fst.comp continuous_snd)
    · exact continuous_fst.dist (continuous_fst.comp continuous_snd)
  have key : {p : Eucl N × (Fin (m + 1) → Eucl N) | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) =
        (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))} =
      ⋃ n, ⋃ l : ℕ, Prod.snd '' C n l := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨x, hxE, hxa, hxδ, hL⟩
      rw [← hKE, mem_iUnion] at hxE
      obtain ⟨n, hn⟩ := hxE
      have hd0 : 0 < dist x p.1 := dist_pos.2 hxa
      have hmin : 0 < min (dist x p.1) (δ - dist x p.1) := lt_min hd0 (by linarith)
      obtain ⟨l₁, hl₁⟩ := exists_nat_one_div_lt hmin
      obtain ⟨l₂, hl₂⟩ := exists_nat_ge ‖p‖
      refine ⟨n, max l₁ l₂, (x, p), ?_, rfl⟩
      have hle : 1 / ((max l₁ l₂ : ℕ) + 1 : ℝ) ≤ 1 / ((l₁ : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (l₁ : ℝ) ≤ ((max l₁ l₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left l₁ l₂
        linarith
      have h1 := lt_of_le_of_lt hle hl₁
      refine ⟨⟨hn, ?_⟩, ⟨?_, ?_⟩, hL⟩
      · rw [mem_closedBall, dist_zero_right]
        exact hl₂.trans (by exact_mod_cast le_max_right l₁ l₂)
      · exact (h1.trans_le (min_le_left _ _)).le
      · have := h1.trans_le (min_le_right _ _)
        simp only [mem_ofPred_eq]
        linarith
    · rintro ⟨n, l, q, ⟨⟨hq1, -⟩, ⟨hd1, hd2⟩, hL⟩, rfl⟩
      refine ⟨q.1, ?_, ?_, ?_, hL⟩
      · rw [← hKE]; exact mem_iUnion.2 ⟨n, hq1⟩
      · intro h
        have : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
        simp only [mem_ofPred_eq, h, dist_self] at hd1
        linarith
      · have : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
        simp only [mem_ofPred_eq] at hd2
        linarith
  rw [key]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun l =>
    ((hCc n l).image continuous_snd).measurableSet
```

## Key steps

1. Write E = ⋃_n K_n with K_n compact.
2. C_{n,l} := {(x,(a,v)) : x ∈ K_n, 1/(l+1) ≤ |x−a| ≤ δ−1/(l+1), ‖(a,v)‖ ≤ l, L_vx = L_va} is closed and bounded, hence compact.
3. The projection π(C_{n,l}) to (a,v) is compact, hence closed and Borel.
4. W = ⋃_{n,l} π(C_{n,l}) by an Archimedean choice of l, so W is Borel.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `git archive d8d46c9 into /tmp/bft-decomp-1791847446; cmp GMT/Ch06/Submission.lean (workspace) and project/GMT/Ch06/Contract.lean (snapshot) against the scratch copy (identical); lake build GMT.Ch06.Submission (success, 3152 jobs)`
- `rg -n 'theorem ae_ae_comm|theorem measurable_measure_prodMk_left |theorem _root_.Monotone.measure_iUnion|theorem _root_.Directed.measure_iUnion|theorem measure_biUnion_eq_iSup|theorem prod_apply_symm|theorem prod_apply |lemma IsSigmaCompact.image|theorem limsup_add_le|theorem limsup_const_mul_of_ne_top|theorem inner_single_left' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'measure_preimage_add_right|measure_univ_of_isAddLeftInvariant|measure_univ_of_isMulLeftInvariant' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n -i 'mickle|besicovitch.federer|purely.unrectifiable' local-references/197bdd4b88278494/mathlib/Mathlib local-references/197bdd4b88278494/project (no match); rg -n 'IsSigmaCompact.measurableSet' local-references/197bdd4b88278494/mathlib/Mathlib (no match)`
- `rg -n 'def dimensionalDensityQuotient|def realUnitBallVolume' lake-packages-25730c7c/simongmt/Poincare; sed -n 1,70p Chapter01/Densities.lean`
- `python3 verifier/gmt-compare.py contract_scope + child_modules (contract mode) for all 8 child statements; lake env lean Scratch/Chal_*.lean (0 errors)`
- `lake env lean Scratch/Names.lean and Scratch/Inst.lean (#check of the cited lemma names; instance checks for IsAddHaarMeasure, IsAddRightInvariant, SFinite of volume on Fin (m+1) → Eucl N, volume univ = ⊤ on Eucl (m+1), BorelSpace of the product types)`
- `lake env lean Scratch/Assembly.lean (parent from child stubs; #print axioms), Scratch/Iface1.lean (cone_ratio_measurable proved from the limsup_sup_measurable stub; ϑ_j instance), Scratch/Iface2.lean (OuterMeasure.mk + rectifiability_mickle_rado interface; later found vacuous because of a binder capture in the test example, and superseded by the complete slice_density_null proof)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (658 names); byte comparison of reused lean_statement/title/statement against dag.json and the accepted handoffs`
- `lake env lean Verify/AllProofsFull.lean (independent reviewer's complete proofs of all six new children + accepted mickle_rado subtree + parent assembly; 0 errors; #print axioms [propext, Classical.choice, Quot.sound] for every declaration) and Verify/Standalone/<key>.lean for each new child with only its declared siblings stubbed (0 errors)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-trichotomy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1-limsup-eq-iinf-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1/decomposition-v1.json`
- `/tmp/bft-decomp-1791847446/Scratch/Assembly.lean`
- `/tmp/bft-decomp-1791847446/Scratch/Iface1.lean`
- `/tmp/bft-decomp-1791847446/Verify/AllProofsFull.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/slice_density_null.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/limsup_sup_measurable.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract, byte-identical to the workspace Submission.lean and to the scratch copy. Neither the snapshot Mathlib nor the project contains a Besicovitch–Federer, Mickle–Radó or purely-unrectifiable result (rg: no match), and Mathlib has no IsSigmaCompact.measurableSet. So all six new child obligations are genuine; the two accepted declarations rectifiability_mickle_rado and rectifiability_mickle_rado_limsup_eq_iInf are reused with byte-identical types. Every library input cited by the child proofs exists in the pinned environment: measurable_measure_prodMk_left, Measure.prod_apply and prod_apply_symm, Measure.ae_ae_comm (Prod.lean), Monotone.measure_iUnion, Directed.measure_iUnion and measure_biUnion_eq_iSup (Continuity.lean), measure_preimage_add_right and measure_univ_of_isAddLeftInvariant (additive forms of Group/Measure.lean), ENNReal.limsup_const_mul_of_ne_top (Order/Filter/ENNReal.lean), IsSigmaCompact.image, EuclideanSpace.inner_single_left (PiL2.lean:318), and dimensionalDensityQuotient and realUnitBallVolume (SimonGMT Chapter01/Densities.lean:39, Hausdorff.lean:34). ENNReal.limsup_add_le (ENNReal.lean:231) requires CountableInterFilter, which 𝓝[>]0 is not, so fibre_cone_comparison proves limsup subadditivity directly. In the scratch build, all eight child types elaborate in the comparator's exact child scope. The parent compiles from the five stubbed children it uses. Complete single-declaration Lean proofs of all six new children compile against their exact frozen types, using only their declared siblings, and with the accepted mickle_rado subtree the whole tree including Submission.rectifiability_bf_trichotomy compiles with axioms [propext, Classical.choice, Quot.sound].
