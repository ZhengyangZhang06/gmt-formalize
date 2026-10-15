# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.comparison_box-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the selected proof ("the box W"), with the half-width r + 1 replaced by an arbitrary s > r and the ball B := B_ρ(0) taken as given (the selected node chooses ρ with closure W₀ ∪ K ⊆ B_ρ(0)). The selected proof is the project's argument for Simon, Lemma 7.3.5 (book/chapter-07.txt, lines 407–417), whose proof Simon leaves to the reader. No sibling or inherited result is used; all facts are from Mathlib.
Notation. G := span{g_1, …, g_k} = Submodule.span ℝ (Set.range g), p := G.starProjection, q := G^⊥.starProjection (both continuous linear maps ℝ^P → ℝ^P), C_s := {x : |⟨g_i, x⟩| < s for all i}, W := p⁻¹(C_s) ∩ q⁻¹(B_ρ(0)).

1. (C_s is open.) C_s = ⋂_{i ∈ Fin k} {x : |⟨g_i, x⟩| < s} is a finite intersection of sets that are open because x ↦ |⟨g_i, x⟩| is continuous (isOpen_lt). Hence C_s is open (isOpen_iInter_of_finite); B_ρ(0) is open.
2. ((i) W is open.) p and q are continuous, so p⁻¹(C_s) and q⁻¹(B_ρ(0)) are open, and so is their intersection W.
3. (Coordinates control vectors of G.) For every t ∈ G: ‖t‖ ≤ Σ_i |⟨g_i, t⟩|. Indeed, t ∈ span(range g) gives c : Fin k → ℝ with t = Σ_i c_i g_i (Submodule.mem_span_range_iff_exists_fun). By orthonormality ⟨g_i, t⟩ = c_i (Orthonormal.inner_right_fintype) and ‖g_i‖ = 1, so ‖t‖ ≤ Σ_i ‖c_i g_i‖ = Σ_i |c_i| = Σ_i |⟨g_i, t⟩| (norm_sum_le, norm_smul).
4. (W is bounded.) Let x ∈ W. Then p(x) ∈ G (starProjection_apply_mem) and p(x) ∈ C_s, so by step 3 ‖p(x)‖ ≤ Σ_i |⟨g_i, p(x)⟩| ≤ Σ_i s = k·s. Moreover ‖q(x)‖ < ρ since q(x) ∈ B_ρ(0). As x = p(x) + q(x) (starProjection_add_starProjection_orthogonal), ‖x‖ ≤ ‖p(x)‖ + ‖q(x)‖ ≤ k·s + ρ. Hence W ⊆ closedBall(0, k·s + ρ), so W is bounded.
5. ((ii) W ⊂⊂ ℝ^P.) ℝ^P = Euclid P is a proper metric space, so the closure of the bounded set W is compact (Bornology.IsBounded.isCompact_closure), and trivially closure W ⊆ ℝ^P. Thus CompactlyContained W univ.
6. (p does not change the coordinates.) For every x ∈ ℝ^P and every i: ⟨g_i, p(x)⟩ = ⟨p(g_i), x⟩ = ⟨g_i, x⟩. The first equality is the self-adjointness of the orthogonal projection (inner_starProjection_left_eq_right); the second holds because g_i ∈ G (Submodule.subset_span), so p(g_i) = g_i (starProjection_eq_self_iff).
7. ((iii) The slab over K lies in W.) Let K ⊆ B_ρ(0) and let x satisfy |⟨g_i, x⟩| ≤ r for all i and q(x) ∈ K. By step 6, |⟨g_i, p(x)⟩| = |⟨g_i, x⟩| ≤ r < s for every i, so p(x) ∈ C_s; and q(x) ∈ K ⊆ B_ρ(0). Hence x ∈ W. ∎

Formalization sketch (context, not part of the numbered proof). The following Lean proof of exactly the frozen type compiled during decomposition (Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, in namespace GMT.Ch07 with the contract opens), with every cited Submission.* dependency present as a stub of its exact frozen type:
theorem Submission.dimred_cs_sos_mt_cm_comparison_box : ∀ (P k : ℕ) (g : Fin k → Euclid P) (r s ρ : ℝ), Orthonormal ℝ g → r < s → IsOpen ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' ball (0 : Euclid P) ρ) ∧ CompactlyContained ((Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' ball (0 : Euclid P) ρ) univ ∧ ∀ K : Set (Euclid P), K ⊆ ball (0 : Euclid P) ρ → {x | ∀ i, |inner ℝ (g i) x| ≤ r} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' K ⊆ (Submodule.span ℝ (Set.range g)).starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' ball (0 : Euclid P) ρ := by
  intro P k g r s ρ hg hrs
  set G := Submodule.span ℝ (Set.range g) with hGdef
  have hCo : IsOpen {x : Euclid P | ∀ i, |inner ℝ (g i) x| < s} := by
    have hset : {x : Euclid P | ∀ i, |inner ℝ (g i) x| < s} = ⋂ i, {x | |inner ℝ (g i) x| < s} := by
      ext x; simp
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_const.inner continuous_id).abs continuous_const
  have hWo : IsOpen (G.starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩
      Gᗮ.starProjection ⁻¹' ball (0 : Euclid P) ρ) :=
    (hCo.preimage G.starProjection.continuous).inter
      (isOpen_ball.preimage Gᗮ.starProjection.continuous)
  -- a vector of G is controlled by its coordinates ⟪g i, ·⟫
  have hcoord : ∀ t ∈ G, ‖t‖ ≤ ∑ i, |inner ℝ (g i) t| := by
    intro t ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 ht
    calc ‖∑ i, c i • g i‖ ≤ ∑ i, ‖c i • g i‖ := norm_sum_le _ _
      _ = ∑ i, |inner ℝ (g i) (∑ j, c j • g j)| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, hg.1 i, mul_one, hg.inner_right_fintype c i, Real.norm_eq_abs]
  have hbdd : Bornology.IsBounded (G.starProjection ⁻¹' {x | ∀ i, |inner ℝ (g i) x| < s} ∩
      Gᗮ.starProjection ⁻¹' ball (0 : Euclid P) ρ) := by
    rw [isBounded_iff_subset_closedBall 0]
    refine ⟨k * s + ρ, fun x hx => ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖G.starProjection x‖ ≤ k * s := by
      calc ‖G.starProjection x‖ ≤ ∑ i, |inner ℝ (g i) (G.starProjection x)| :=
            hcoord _ (G.starProjection_apply_mem x)
        _ ≤ ∑ _i : Fin k, s := Finset.sum_le_sum fun i _ => (hx.1 i).le
        _ = k * s := by simp
    have h2 : ‖Gᗮ.starProjection x‖ < ρ := by simpa using hx.2
    calc ‖x‖ = ‖G.starProjection x + Gᗮ.starProjection x‖ := by
          rw [G.starProjection_add_starProjection_orthogonal]
      _ ≤ ‖G.starProjection x‖ + ‖Gᗮ.starProjection x‖ := norm_add_le _ _
      _ ≤ k * s + ρ := by linarith
  refine ⟨hWo, ⟨hbdd.isCompact_closure, subset_univ _⟩, ?_⟩
  intro K hK x hx
  refine ⟨fun i => ?_, hK hx.2⟩
  have hgi : inner ℝ (g i) (G.starProjection x) = inner ℝ (g i) x := by
    rw [← G.inner_starProjection_left_eq_right,
      G.starProjection_eq_self_iff.mpr (Submodule.subset_span ⟨i, rfl⟩)]
  rw [hgi]
  exact (hx.1 i).trans_lt hrs
(This sketch uses no Submission.* dependency; its #print axioms are propext, Classical.choice, Quot.sound.)

## Key steps

1. C_s is a finite intersection of open sets and p, q are continuous, so W = p⁻¹(C_s) ∩ q⁻¹(B_ρ(0)) is open.
2. For t ∈ span g, t = Σ c_i g_i with c_i = ⟨g_i, t⟩, so ‖t‖ ≤ Σ_i |⟨g_i, t⟩|; hence ‖x‖ ≤ ‖p x‖ + ‖q x‖ ≤ k·s + ρ on W.
3. Bounded sets of the proper space ℝ^P have compact closure: CompactlyContained W univ.
4. ⟨g_i, p x⟩ = ⟨g_i, x⟩ (p self-adjoint, p g_i = g_i), so |⟨g_i, x⟩| ≤ r < s and q x ∈ K ⊆ B_ρ(0) put x in W.

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1 = workspace HEAD, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean and Submission.lean with the workspace copies (identical)`
- `python3 over dag.json: the selected node, its ancestors' depends_on and statuses, the exact lean_statement of all 14 dependency/reuse declarations, accepted nodes whose lean_statement mentions '.support', 'ᶜ = 0', 'cycle', 'competitor' (found dimred_mbl_lc_rc_cycle_competitor, dtc_bc_lc_rc_cycle_competitor, cbrld_ns_support_sub_subset, dimred_mbl_pf_imrep_carrier_mass_support, rsd_imrep_compact_measure_ne_top), and grep -c of the five new dimred_cs_sos_mt_cm_* names (0 hits)`
- `git show 35e359955ef6bac37033306b3f33a12c284b7174:GMT/Ch07/Submission.lean: Submission.dimred_mbl_lc_rc_cycle_competitor present with a type byte-identical to dag.json; its import lines equal the contract's`
- `grep -n over .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean: GeometricCurrentOn, boundary(_apply), zero_apply, ext, massOn, mass, massOn_mono, massAdmissibleOn, VanishesOn, zeroRegion, support, testFormOnInclusion, restrictDomain, IsTestForm`
- `grep -rn over the snapshot mathlib: setIntegral_sdiff, integral_sub, measure_sdiff (measure_diff deprecated), ENNReal.le_of_add_le_add_left, withDensity_absolutelyContinuous, withDensity_apply, Measure.restrict_apply', Measure.restrict_restrict, starProjection_add_starProjection_orthogonal, inner_starProjection_left_eq_right, starProjection_apply_mem, starProjection_eq_self_iff, Submodule.isClosed_orthogonal, Submodule.closed_of_finiteDimensional, Submodule.mem_span_range_iff_exists_fun, Orthonormal.inner_right_fintype, isBounded_iff_subset_ball, isBounded_iff_subset_closedBall, Bornology.IsBounded.isCompact_closure`
- `grep -n '3.5\|left to the reader' book/chapter-07.txt; sed -n 405,420p (Lemma 3.5, proof left to the reader)`
- `lake env lean /tmp/cm-decomp/{T0,Assembly,A,B,D,E,F,Final}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-8a972d0014/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-4725781174/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`

Pins match. The manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c, and the snapshot Contract.lean and Submission.lean are byte-identical to the workspace files. Simon leaves Lemma 7.3.5 to the reader, so the children are extracted from the supplied project proof. Neither SimonGMT nor the snapshot mathlib contains the five new statements, and their names are unused in dag.json and the snapshot. One accepted declaration fits exactly: Submission.dimred_mbl_lc_rc_cycle_competitor (accepted; candidate 35e35995; type byte-identical; contract imports). It is reused as the Step 4 child. Other accepted lemmas found (cbrld_ns_support_sub_subset, dimred_mbl_pf_imrep_carrier_mass_support, rsd_imrep_compact_measure_ne_top) are not ancestor dependencies. Their content is covered in a few lines inside carried_transfer and box_cancellation, so they are not added. The snapshot mathlib supplies every library fact the child proofs use, under the names cited, including setIntegral_sdiff, measure_sdiff, ENNReal.le_of_add_le_add_left, starProjection_add_starProjection_orthogonal, inner_starProjection_left_eq_right, Submodule.mem_span_range_iff_exists_fun, Orthonormal.inner_right_fintype and Bornology.IsBounded.isCompact_closure. Lean check (Final.lean): the 5 new children are proved from stubs of exactly their cited dependencies, and the frozen parent type is proved from the child and dependency stubs. It compiles with no errors; sorry occurs only in the 14 stubs.
