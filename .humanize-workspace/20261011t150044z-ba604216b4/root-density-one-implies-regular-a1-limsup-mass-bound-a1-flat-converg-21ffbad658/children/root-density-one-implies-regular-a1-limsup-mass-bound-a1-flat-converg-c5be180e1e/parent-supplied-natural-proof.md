# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.good_center-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.good_center-a1.tube_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to Geometric Measure Theory, Ch. 6, proof of the Deformation Theorem 5.1, the identity stated just before display (6) (book/chapter-06.txt lines 1704–1709). It writes the open tube of radius t about the shifted dual skeleton L*(a) = a + L*_{ℓ−1} as ⋃_{j=1}^{N} ⋃_{z ∈ ℤ^{n+ℓ} ∩ S_j} p_j^{-1}(B_t(p_j(a) + z)). The text extraction renders the skeleton as "Lk 1 (a)" and drops the radius glyph; we write t. The shifted dual skeleton and its tubes are introduced in the notation before Lemma 5.4 (lines 1482–1490), and display (2) of the proof of 5.4 (line 1524) describes the skeleton as ⋃_{j=1}^{N} ⋃_{z} (z + p_j^{-1}(p_j(a))).

This lemma is the inclusion "⊆" of step 1 (tube description) of the supplied proof of the good-centre lemma Submission.dor_lmb_fcd_good_center, written in coordinates. Step 5 of that proof uses only this inclusion, through the subadditivity bound μ({d_a < r}) ≤ Σ_J μ(⋃_z p_J^{-1}(B_r(p_J(a) + z))). For an (m+2)-set J of coordinate indices with injective enumeration e : Fin (m+2) → Fin P, the orthogonal projection p_J onto the coordinate plane S_J is recorded by y ↦ (y_{e(k)})_k, and |p_J(x) − p_J(a) − z|² = Σ_k (x_{e(k)} − a_{e(k)} − z_k)². Step 1 of the supplied proof computes dist(x, A_{J,z}) = |p_J(x) − p_J(a) − z| exactly. Only the half of that computation giving "⊆" is needed here: |p_J(x − w)| ≤ |x − w| for a near point w ∈ L*(a).

Notation. For v ∈ Euclid P = ℝ^P write v_i for its i-th coordinate (i ∈ Fin P). dist is the Euclidean distance, dist(x, w) = √(Σ_i (x_i − w_i)²) (Mathlib EuclideanSpace.dist_eq). L*(a) := {w : there is a finite s ⊆ Fin P with |s| ≥ m + 2 and w_i − a_i ∈ ℤ for all i ∈ s}, the set in the statement.

1. L*(a) is nonempty: a ∈ L*(a), witnessed by s := Fin P (all indices). Then |s| = P ≥ m + 2 because m + 1 < P, and a_i − a_i = 0 is the integer 0 for every i.
2. Since L*(a) ≠ ∅ and infDist(x, L*(a)) < r, Metric.infDist_lt_iff (which needs the nonemptiness from 1) gives w ∈ L*(a) with dist(x, w) < r. Fix a finite set s ⊆ Fin P with |s| ≥ m + 2 and w_i − a_i ∈ ℤ for all i ∈ s.
3. Since m + 2 ≤ |s|, Finset.exists_subset_card_eq gives J ⊆ s with |J| = m + 2. Let e : Fin (m + 2) → Fin P be the increasing enumeration of J (e(k) := J.orderEmbOfFin _ k). Then e is injective and e(k) ∈ J ⊆ s for every k.
4. For every k ∈ Fin (m + 2) we have e(k) ∈ s, so we may choose z_k ∈ ℤ with w_{e(k)} − a_{e(k)} = z_k. Then x_{e(k)} − a_{e(k)} − z_k = x_{e(k)} − w_{e(k)} for every k.
5. Put f(i) := (x_i − w_i)² ≥ 0 for i ∈ Fin P. Since e is injective, Σ_k f(e(k)) = Σ_{i ∈ e(Fin (m+2))} f(i) (Finset.sum_map along the embedding e). Since e(Fin (m+2)) ⊆ Fin P and f ≥ 0, this is at most Σ_{i ∈ Fin P} f(i) (Finset.sum_le_sum_of_subset_of_nonneg).
6. By EuclideanSpace.dist_eq and nonnegativity of the radicand, Σ_i f(i) = dist(x, w)². Since 0 ≤ dist(x, w) < r, dist(x, w)² < r².
7. By 4, 5 and 6, Σ_k (x_{e(k)} − a_{e(k)} − z_k)² = Σ_k f(e(k)) ≤ Σ_i f(i) = dist(x, w)² < r². So e is injective and z = (z_k)_k ∈ ℤ^{Fin (m+2)} satisfies Σ_k (x_{e(k)} − a_{e(k)} − z_k)² < r², which is the claim. (No sign condition on r is needed: the witness w forces r > dist(x, w) ≥ 0.) ∎

Appendix (supplementary, machine-checked; not needed for the argument above). The following Lean 4 declaration, placed in GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` after the contract's closing `end` of the noncomputable section (so with the contract's `open`s), follows the numbered steps above and adds no helper declaration. It was compiled with `lake env lean` against the pinned workspace (Lean v4.35.0-rc3, Mathlib 25730c7c), alone and inserted into a copy of GMT/Ch07/Submission.lean; `#print axioms` reports only propext, Classical.choice, Quot.sound.

/-- **Tube about the shifted dual skeleton** (Simon Ch. 6, proof of 5.1, the identity before
display (6), inclusion `⊆`).  Let `L*(a)` be the set of `w` with `w_i − a_i ∈ ℤ` for at least
`m + 2` indices `i`.  It contains `a`, so `infDist x L*(a) < r` gives `w ∈ L*(a)` with
`|x − w| < r`.  Enumerate `m + 2` of the indices of `w` by `e`, and put
`z_k = w_{e(k)} − a_{e(k)} ∈ ℤ`.  Then
`Σ_k (x_{e(k)} − a_{e(k)} − z_k)² = Σ_k (x_{e(k)} − w_{e(k)})² ≤ |x − w|² < r²`. -/
theorem Submission.dor_lmb_fcd_gc_tube_cover : ∀ (P m : ℕ), m + 1 < P → ∀ (a x : Euclid P) (r : ℝ), infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r → ∃ e : Fin (m + 2) → Fin P, Function.Injective e ∧ ∃ z : Fin (m + 2) → ℤ, ∑ k, (x (e k) - a (e k) - z k) ^ 2 < r ^ 2 := by
  classical
  intro P m hPm a x r hx
  set L := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- Steps 1–2: `a ∈ L*(a)` (all `P ≥ m + 2` indices), so some `w ∈ L*(a)` has `|x − w| < r`
  have hne : L.Nonempty := ⟨a, Finset.univ, by simp; omega, fun i _ => ⟨0, by simp⟩⟩
  obtain ⟨w, ⟨s, hs, hsz⟩, hxw⟩ := (infDist_lt_iff hne).1 hx
  -- Step 3: `m + 2` of the indices in `s`, enumerated injectively by `e`
  obtain ⟨J, hJs, hJ⟩ := Finset.exists_subset_card_eq hs
  let e : Fin (m + 2) → Fin P := fun k => J.orderEmbOfFin hJ k
  have he : Function.Injective e := (J.orderEmbOfFin hJ).injective
  have hes : ∀ k, e k ∈ s := fun k => hJs (J.orderEmbOfFin_mem hJ k)
  -- Step 4: `z_k = w_{e(k)} − a_{e(k)} ∈ ℤ`
  choose z hz using fun k => hsz (e k) (hes k)
  refine ⟨e, he, z, ?_⟩
  have hterm : ∀ k, x (e k) - a (e k) - z k = x (e k) - w (e k) := fun k => by
    rw [← hz k]; ring
  -- Step 5: the `m + 2` selected squares are among the `P` nonnegative squares
  have hsub : ∑ k, (x (e k) - w (e k)) ^ 2 ≤ ∑ i, (x i - w i) ^ 2 := by
    have := Finset.sum_map Finset.univ ⟨e, he⟩ (fun i => (x i - w i) ^ 2)
    simp only [Function.Embedding.coeFn_mk] at this
    rw [← this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => sq_nonneg _
  -- Step 6: `Σ_i (x_i − w_i)² = |x − w|²`
  have hdist : ∑ i, (x i - w i) ^ 2 = dist x w ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Real.dist_eq, sq_abs]
  have h0 : 0 ≤ dist x w := dist_nonneg
  -- Step 7
  calc ∑ k, (x (e k) - a (e k) - z k) ^ 2 = ∑ k, (x (e k) - w (e k)) ^ 2 := by
        simp_rw [hterm]
    _ ≤ ∑ i, (x i - w i) ^ 2 := hsub
    _ = dist x w ^ 2 := hdist
    _ < r ^ 2 := by nlinarith

## Key steps

1. a ∈ L*(a) because m + 2 ≤ P, so infDist(x, L*(a)) < r gives w ∈ L*(a) with dist(x, w) < r (Metric.infDist_lt_iff).
2. Choose m + 2 of the indices i with w_i − a_i ∈ ℤ (Finset.exists_subset_card_eq), let e be their injective increasing enumeration, and put z_k := w_{e(k)} − a_{e(k)} ∈ ℤ.
3. Σ_k (x_{e(k)} − a_{e(k)} − z_k)² = Σ_k (x_{e(k)} − w_{e(k)})² ≤ Σ_i (x_i − w_i)² = dist(x, w)² < r².

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c)`
- `cmp project/GMT/Ch07/Contract.lean <workspace>/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (both identical)`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement|theorem volume_pi_ball|theorem volume_pi_Ioo|theorem volume_preserving_piEquivPiSubtypeProd|theorem volume_measurePreserving_piCongrLeft|theorem infDist_lt_iff|theorem le_map_apply|theorem measure_iUnion_fintype_le|theorem measure_biUnion_le|theorem measure_biUnion |theorem measure_preimage_equiv" mathlib/Mathlib -g '*.lean'`
- `rg -n "volume_preserving_symm_measurableEquiv_toLp|PairwiseDisjoint.countable_of_isOpen|theorem prod_prod |exists_subset_card_eq|lemma dist_pi_lt_iff|orderEmbOfFin_mem|theorem EuclideanSpace.dist_eq|isFiniteMeasure_map" mathlib/Mathlib`
- `rg -l -i "good.?center|dual skeleton|deformation" project -g '*.lean'`
- `rg -n -i "good.?center|dual skeleton|deformation|latticeFace" project/GMT/Ch06/Contract.lean`
- `rg -n -i "Vitali|exists_disjoint_subfamily" project -g '*.lean'`
- `python3 -I scans of dag.json (2050 nodes at 2026-10-13T22:12Z): lean_name/status/candidate_commit of cmcdt_gc_tube_cover, cmcdt_gc_bad_set_volume, cmcdt_gc_cube_selection, cmcdt_good_center, dimred_mbl_dt_good_center, dor_lmb_fcd_good_center; occurrences of dor_lmb_fcd_gc_tube_cover/bad_set_volume/cube_selection (none)`
- `git log --all -S'dor_lmb_fcd_gc_' over 7825 refs (no hit); grep dor_lmb_fcd_gc_ in GMT/Ch07/Submission.lean of 1791 git worktrees (no hit); grep -rl dor_lmb_fcd_gc_ nodes/ (only this node's rejected decomposition-v1.json)`
- `git diff <c>^ <c> -- GMT/Ch07/Submission.lean for accepted candidates e26fd126f, 95867e156, e55d09573 (the cmcdt_gc_* proofs reused, renamed, as Lean appendices)`
- `python3 -I parse of nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/decomposition-v2.json + decomposition-audit-v2.json and nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9b0e7b29a0/decomposition-v1.json + decomposition-audit-v1.json (identical child types, audits passed)`
- `sed -n 1470,1530p and 1651,1725p book/chapter-06.txt; sed -n 605,660p book/chapter-01.txt`
- `sed -n 1380,1570p and 6600,6800p /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py; grep -n 'def _accepted_checkpoint' (name-reservation rule, max_depth gate)`
- `contract_scope() of verifier/gmt-compare.py on GMT/Ch07/Contract.lean; lake env lean /tmp/gc2-lean/{Challenge_tube,Challenge_bad,Challenge_cube,Challenge_parent,RealBuild,StubBuild,SubmissionInserted,FromDraft2}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch01/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-21ffbad658/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-21ffbad658/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9b0e7b29a0/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9b0e7b29a0/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

Snapshot: project b4d606db, mathlib 25730c7c; its GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. No Lean declaration of the good-centre averaging argument (Simon 6.5.1 (1)–(7)) exists in the snapshot project: the only deformation-theorem material is the sorry-frozen latticeFace/IsLatticeChain/DeformationTheorem definitions of GMT/Ch06/Contract.lean (not imported by GMT.Ch07.Submission), and the only Vitali material is Ch01's HasSymmetricVitaliProperty definition. Every Mathlib lemma used by the three children and the assembly exists in the pinned snapshot: Vitali.exists_disjoint_subfamily_covering_enlargement (Covering/Vitali.lean:59), Real.volume_pi_ball (Measure/Lebesgue/Basic.lean:272), Real.volume_pi_Ioo (:244), volume_preserving_piEquivPiSubtypeProd (Constructions/Pi.lean:726), volume_measurePreserving_piCongrLeft (:740), EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Measure/Haar/InnerProductSpace.lean:124), Metric.infDist_lt_iff (HausdorffDistance.lean:513), Measure.le_map_apply (Measure/Map.lean:218), measure_iUnion_fintype_le and measure_biUnion_le (OuterMeasure/Basic.lean:84, :74), measure_biUnion (Measure/Basic.lean:132), Set.PairwiseDisjoint.countable_of_isOpen (Topology/Bases.lean:487), Measure.prod_prod for arbitrary sets (Measure/Prod.lean:231), MeasurePreserving.measure_preimage_equiv (Dynamics/Ergodic/MeasurePreserving.lean:155), EuclideanSpace.dist_eq (InnerProductSpace/PiL2.lean:158), dist_pi_lt_iff (MetricSpace/Pseudo/Pi.lean:67), Finset.exists_subset_card_eq (Finset/Card.lean:677), Finset.orderEmbOfFin_mem (Finset/Sort.lean:211), Measure.isFiniteMeasure_map (Measure/Typeclasses/Finite.lean:124). Reuse: the three child types are byte-identical to the accepted cmcdt_gc_* nodes (candidates e26fd126f, 95867e156, e55d09573) and to the audited dimred_mbl_dt_gc_* split, but the runtime refused reuse of cmcdt_gc_tube_cover under this parent, so fresh dor_lmb_fcd_gc_* names (absent from dag.json, all git refs and all worktrees) are used and the accepted proofs are supplied, renamed, as Lean appendices. All four exact comparator challenges, the real build, the stub build and the in-place insertion into a Submission.lean copy compile; axioms [propext, Classical.choice, Quot.sound].
