# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.good_center-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.good_center-a1.bad_set_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to Geometric Measure Theory, Ch. 6, proof of the deformation theorem 5.1 (book/chapter-06.txt lines 1651–1691): the definition (1) of the good set G_j, the claim (2) that the bad set B_j has small L^{n+1}-measure, display (3), the 5-times covering lemma (Ch. 1, 3.4) giving (4), and the summation after (4). That summation uses the pairwise disjointness of the sets p_j^{-1}(B_{s_l}(b_l + z)). We write Simon's radii as s, s_l because ρ denotes the measure here. This is step 2b of the parent proof (the good-centre lemma, Submission.dimred_mbl_dt_good_center), applied to the image measure ρ = p_J#ν on the coordinate plane S_J ≅ ℝ^d (d = n + 1 = m + 2 in the parent).

Departures from the printed text and from step 2b, none of which changes the argument:
(i) The covering balls are balls of Mathlib's sup metric on ℝ^d = Fin d → ℝ, i.e. open cubes of volume (2r)^d. They contain the Euclidean balls of the same radius. Simon and the parent use Euclidean balls B_s(b) ⊂ S_j, of volume ω_{n+1}s^{n+1}. Simon's covering lemma (Ch. 1, 3.4, book/chapter-01.txt lines 612–623) is stated for balls in an arbitrary metric space X, so it applies verbatim to the sup metric. The periodic sets O_r(g) are still unions of Euclidean balls, as in (1).
(ii) The centres range over the open cube (1/4, 3/4)^d, i.e. |g_k − 1/2| < 1/4, instead of F_j ∩ B_{1/4}(x_j). This is the condition the parent needs. The radii range over (0, 1/4], as in step 2 of the parent proof.
(iii) Only the centres g ∈ Bad have to be covered, not the whole balls. The 5-times covering lemma (Ch. 1, 3.4) says the balls meet and r_g ≤ 2 r_b; in Mathlib this is Vitali.exists_disjoint_subfamily_covering_enlargement with τ = 2. For centres alone it gives Bad ⊆ ⋃_b ball(b, 3 r_b) (step 6). Printed (4) and step 2b of the parent use the factor 5, which the lemma provides for the whole balls. With cube volumes (2r)^d, the printed bound L^{n+1}(B_j) ≤ 20^{n+1}β^{-1}ω_{n+1}(1/4)^{n+1} = 5^{n+1}ω_{n+1}/β of (2) becomes 6^d/β ≤ 10^d/β.
(iv) M(T) is replaced by ρ(ℝ^d).
(v) The bad set never has to be measurable: only monotonicity and countable subadditivity of the outer measure volume are used. So step 2a of the parent proof (relative openness of B_J) is not needed. This repairs a gap in the book, which never shows B_j to be measurable.
Only (v) repairs the book. Departures (i)–(iv) are not corrections, since Simon's argument with Euclidean balls is valid, and (iv) is only notation. They are stated explicitly as specialisations to the frozen contract: the parent needs only the cube condition on the centres, and the pinned Mathlib's metric on ℝ^d = Fin d → ℝ is the sup metric, so the covering lemma is applied to its balls. The covering and packing argument itself is Simon's.

Notation. ℝ^d := Fin d → ℝ, with volume the product Lebesgue measure and Mathlib's sup metric dist(g, h) = max_k |g_k − h_k| (0 if d = 0). For r > 0, ball(g, r) = {h : |h_k − g_k| < r for all k} (dist_pi_lt_iff); it is open and volume(ball(g, r)) = (2r)^d (Real.volume_pi_ball). For g ∈ ℝ^d and r ∈ ℝ put O_r(g) := {y : ∃ z ∈ ℤ^d, Σ_k (y_k − g_k − z_k)² < r²}. "Bad" is the set in the statement. All inequalities between measures are in [0, ∞], with real factors embedded by ENNReal.ofReal.

1. Every O_r(g) is open, hence Borel. It is the union over z ∈ ℤ^d of the sets {y : Σ_k (y_k − g_k − z_k)² < r²}, each the preimage of the open set (−∞, r²) under a continuous function.
2. If ρ(ℝ^d) = 0, then Bad = ∅: for any g and r we would need β r^d · 0 = 0 < ρ(O_r(g)) ≤ ρ(ℝ^d) = 0, which is impossible. Then volume(Bad) = 0 ≤ 10^d/β. From now on assume ρ(ℝ^d) ≠ 0; also ρ(ℝ^d) ≠ ∞ because ρ is finite.
3. (Printed (3).) For every g ∈ Bad choose r_g with 0 < r_g ≤ 1/4 and β r_g^d ρ(ℝ^d) < ρ(O_{r_g}(g)); this is possible by the definition of Bad.
4. (Covering lemma.) Apply Vitali.exists_disjoint_subfamily_covering_enlargement to the sets B(g) := ball(g, r_g), g ∈ Bad, with δ(g) := r_g, τ := 2 and R := 1/4. Its hypotheses hold: 1 < 2, 0 ≤ r_g ≤ 1/4, and g ∈ ball(g, r_g) because r_g > 0. It gives u ⊆ Bad such that the balls ball(b, r_b), b ∈ u, are pairwise disjoint, and every g ∈ Bad has some b ∈ u with ball(g, r_g) ∩ ball(b, r_b) ≠ ∅ and r_g ≤ 2 r_b.
5. u is countable, because the sets ball(b, r_b), b ∈ u, are open, nonempty and pairwise disjoint in the separable space ℝ^d (Set.PairwiseDisjoint.countable_of_isOpen).
6. (Printed (4), with 3 in place of 5.) Bad ⊆ ⋃_{b ∈ u} ball(b, 3 r_b). Given g ∈ Bad, take b ∈ u and y ∈ ball(g, r_g) ∩ ball(b, r_b) as in 4. Then dist(g, b) ≤ dist(g, y) + dist(y, b) < r_g + r_b ≤ 2 r_b + r_b = 3 r_b.
7. (Printed "pairwise disjoint collection".) If b, b' ∈ u and b ≠ b', then O_{r_b}(b) ∩ O_{r_{b'}}(b') = ∅. Suppose y lies in both, with z, z' ∈ ℤ^d such that Σ_k (y_k − b_k − z_k)² < r_b² and Σ_k (y_k − b'_k − z'_k)² < r_{b'}². Each square is at most the sum of these nonnegative squares, so |y_k − b_k − z_k| < r_b and |y_k − b'_k − z'_k| < r_{b'} for every k. Fix k. Since b, b' ∈ Bad, 1/4 < b_k, b'_k < 3/4, and r_b, r_{b'} ≤ 1/4. Hence z_k < y_k < z_k + 1 and z'_k < y_k < z'_k + 1, so z_k < z'_k + 1 and z'_k < z_k + 1. For integers this means z_k = z'_k; thus z = z'. Then v := (y_k − z_k)_k satisfies |v_k − b_k| = |y_k − b_k − z_k| < r_b and |v_k − b'_k| < r_{b'} for every k, i.e. v ∈ ball(b, r_b) ∩ ball(b', r_{b'}). This contradicts the pairwise disjointness in 4.
8. (Summation.) Put S := Σ_{b ∈ u} β r_b^d ∈ [0, ∞], a countable sum. Step 3 gives the first inequality below. Steps 7, 1 and 5 give the equality, by countable additivity over the pairwise disjoint Borel sets O_{r_b}(b), b ∈ u (measure_biUnion). Monotonicity gives the last inequality:
 S · ρ(ℝ^d) = Σ_{b∈u} β r_b^d ρ(ℝ^d) ≤ Σ_{b∈u} ρ(O_{r_b}(b)) = ρ(⋃_{b∈u} O_{r_b}(b)) ≤ ρ(ℝ^d) = 1 · ρ(ℝ^d).
 Since 0 ≠ ρ(ℝ^d) ≠ ∞ we may cancel, so S ≤ 1 (ENNReal.mul_le_mul_iff_left).
9. (Volume bound.) Step 6, monotonicity, countable subadditivity over the countable set u (measure_biUnion_le) and the ball-volume formula give
 volume(Bad) ≤ Σ_{b∈u} volume(ball(b, 3 r_b)) = Σ_{b∈u} (6 r_b)^d = Σ_{b∈u} (6^d/β) · β r_b^d = (6^d/β) · S ≤ 6^d/β ≤ 10^d/β.
 Here (6 r_b)^d = (6^d/β)(β r_b^d) because β > 0, and ofReal(st) = ofReal(s) ofReal(t) for s, t ≥ 0. This is the claim. ∎

Appendix (supplementary, machine-checked; not needed for the argument above). The following Lean 4 declaration, placed in GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` after the contract's closing `end` of the noncomputable section (so with the contract's `open`s), follows the numbered steps above. It was compiled with `lake env lean` against the pinned workspace (Lean v4.35.0-rc3, Mathlib 25730c7c); `#print axioms` reports only propext, Classical.choice, Quot.sound.

theorem Submission.dimred_mbl_dt_gc_bad_set_volume : ∀ (d : ℕ) (ρ : Measure (Fin d → ℝ)), IsFiniteMeasure ρ → ∀ β : ℝ, 0 < β → volume {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ENNReal.ofReal (β * r ^ d) * ρ univ < ρ {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}} ≤ ENNReal.ofReal (10 ^ d / β) := by
  classical
  intro d ρ hρ β hβ
  set O : (Fin d → ℝ) → ℝ → Set (Fin d → ℝ) := fun g r =>
    {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} with hO
  set Bad := {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r)} with hBad
  -- the periodic sets are open
  have hOopen : ∀ g r, IsOpen (O g r) := by
    intro g r
    have : O g r = ⋃ z : Fin d → ℤ, {y | ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} := by
      ext y; simp [hO]
    rw [this]
    exact isOpen_iUnion fun z => isOpen_lt (by fun_prop) continuous_const
  -- Step 1: if `ρ(ℝ^d) = 0` the bad set is empty
  by_cases h0 : ρ univ = 0
  · have : Bad = ∅ := by
      ext g
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨-, r, -, -, hr⟩
      rw [h0, mul_zero, measure_mono_null (subset_univ _) h0] at hr
      exact lt_irrefl _ hr
    rw [this, measure_empty]
    exact bot_le
  have hfin : ρ univ ≠ ∞ := measure_ne_top ρ univ
  -- Step 2: radii
  have hrad : ∀ g ∈ Bad, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r) := fun g hg => hg.2
  choose! rad hrad0 hrad1 hradlt using hrad
  -- Step 3: Vitali
  obtain ⟨u, huBad, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun g => ball g (rad g)) Bad rad 2 one_lt_two (fun g hg => (hrad0 g hg).le) (1 / 4) hrad1
    (fun g hg => ⟨g, mem_ball_self (hrad0 g hg)⟩)
  -- Step 4: `u` is countable
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun g hg => ⟨g, mem_ball_self (hrad0 g (huBad hg))⟩)
  -- Step 5: covering by the enlarged balls
  have hBadsub : Bad ⊆ ⋃ b ∈ u, ball b (3 * rad b) := by
    intro g hg
    obtain ⟨b, hbu, ⟨y, hy1, hy2⟩, hle⟩ := hucov g hg
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hy1 hy2 ⊢
    calc dist g b ≤ dist g y + dist y b := dist_triangle _ _ _
      _ < rad g + rad b := by rw [dist_comm g y]; exact add_lt_add hy1 hy2
      _ ≤ 3 * rad b := by linarith
  -- Step 6: disjointness of the periodic sets
  have hcoord : ∀ (y g : Fin d → ℝ) (r : ℝ) (z : Fin d → ℤ),
      ∑ k, (y k - g k - z k) ^ 2 < r ^ 2 → 0 < r → ∀ k, |y k - g k - z k| < r := by
    intro y g r z h hr k
    have hk : (y k - g k - z k) ^ 2 < r ^ 2 :=
      lt_of_le_of_lt (Finset.single_le_sum (f := fun i => (y i - g i - z i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ k)) h
    exact abs_lt_of_sq_lt_sq hk hr.le
  have hOdisj : u.PairwiseDisjoint fun b => O b (rad b) := by
    intro b hb b' hb' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨z, hz⟩ ⟨z', hz'⟩
    have hb0 := hrad0 b (huBad hb)
    have hb'0 := hrad0 b' (huBad hb')
    have h1 := hcoord y b (rad b) z hz hb0
    have h2 := hcoord y b' (rad b') z' hz' hb'0
    have hr1 := hrad1 b (huBad hb)
    have hr2 := hrad1 b' (huBad hb')
    have hzz : z = z' := by
      funext k
      have a1 := abs_lt.1 (h1 k)
      have a2 := abs_lt.1 (h2 k)
      have a3 := abs_lt.1 ((huBad hb).1 k)
      have a4 := abs_lt.1 ((huBad hb').1 k)
      have c1 : (z k : ℝ) < z' k + 1 := by linarith
      have c2 : (z' k : ℝ) < z k + 1 := by linarith
      have c1' : z k < z' k + 1 := by exact_mod_cast c1
      have c2' : z' k < z k + 1 := by exact_mod_cast c2
      omega
    subst hzz
    have hv : (fun k => y k - z k) ∈ ball b (rad b) ∩ ball b' (rad b') := by
      constructor
      · rw [mem_ball, dist_pi_lt_iff hb0]
        intro k
        rw [Real.dist_eq]
        have := h1 k
        rwa [show y k - z k - b k = y k - b k - z k by ring]
      · rw [mem_ball, dist_pi_lt_iff hb'0]
        intro k
        rw [Real.dist_eq]
        have := h2 k
        rwa [show y k - z k - b' k = y k - b' k - z k by ring]
    exact (Set.disjoint_left.1 (hudisj hb hb' hne)) hv.1 hv.2
  -- Step 7: the sum of `β r_b^d` is at most `1`
  set S : ℝ≥0∞ := ∑' b : u, ENNReal.ofReal (β * rad b ^ d) with hS
  have hSle : S ≤ 1 := by
    have hsum : S * ρ univ ≤ 1 * ρ univ := by
      calc S * ρ univ = ∑' b : u, ENNReal.ofReal (β * rad b ^ d) * ρ univ :=
            (ENNReal.tsum_mul_right).symm
        _ ≤ ∑' b : u, ρ (O b (rad b)) :=
            ENNReal.tsum_le_tsum fun b => (hradlt b (huBad b.2)).le
        _ = ρ (⋃ b ∈ u, O b (rad b)) :=
            (measure_biUnion hucount hOdisj fun b _ => (hOopen _ _).measurableSet).symm
        _ ≤ ρ univ := measure_mono (subset_univ _)
        _ = 1 * ρ univ := (one_mul _).symm
    exact (ENNReal.mul_le_mul_iff_left h0 hfin).1 hsum
  -- Step 8: the volume estimate
  calc volume Bad ≤ volume (⋃ b ∈ u, ball b (3 * rad b)) := measure_mono hBadsub
    _ ≤ ∑' b : u, volume (ball (b : Fin d → ℝ) (3 * rad b)) := measure_biUnion_le _ hucount _
    _ = ∑' b : u, ENNReal.ofReal (6 ^ d / β) * ENNReal.ofReal (β * rad b ^ d) := by
        refine tsum_congr fun b => ?_
        have hb0 := hrad0 b (huBad b.2)
        rw [Real.volume_pi_ball _ (by positivity), Fintype.card_fin,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ENNReal.ofReal (6 ^ d / β) * S := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (6 ^ d / β) * 1 := by gcongr
    _ ≤ ENNReal.ofReal (10 ^ d / β) := by
        rw [mul_one]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        norm_num

## Key steps

1. If ρ(ℝ^d) = 0 the bad set is empty. Otherwise choose for each bad g a radius r_g ∈ (0, 1/4] with β r_g^d ρ(ℝ^d) < ρ(O_{r_g}(g)) (printed (3)).
2. Vitali (Vitali.exists_disjoint_subfamily_covering_enlargement, τ = 2) on the sup-metric balls ball(g, r_g) gives a pairwise disjoint subfamily ball(b, r_b), b ∈ u. It is countable by separability, and Bad ⊆ ⋃_{b∈u} ball(b, 3 r_b) (printed (4)).
3. For b ≠ b' in u the periodic sets O_{r_b}(b) and O_{r_{b'}}(b') are disjoint. The centres lie in (1/4, 3/4)^d and the radii are ≤ 1/4, so any common point forces equal integer shifts, which reduces to the disjoint balls.
4. Summation: Σ_b β r_b^d ρ(ℝ^d) ≤ Σ_b ρ(O_{r_b}(b)) = ρ(⋃_b O_{r_b}(b)) ≤ ρ(ℝ^d), so Σ_b β r_b^d ≤ 1.
5. volume(Bad) ≤ Σ_b volume(ball(b, 3 r_b)) = Σ_b (6 r_b)^d = (6^d/β) Σ_b β r_b^d ≤ 6^d/β ≤ 10^d/β.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C SNAPSHOT/mathlib rev-parse HEAD and git -C SNAPSHOT/project rev-parse HEAD (both match); git rev-parse HEAD in workspaces/gmt-ch07 (b4d606db) and in .lake/packages/mathlib (25730c7c) and .lake/packages/simongmt (2b366308)`
- `cmp SNAPSHOT/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n -i 'vitali|good.?cent|dual skeleton|bad.?set|dimred_mbl_dt_gc' SNAPSHOT/project -g '*.lean' (only the Ch01 HasSymmetricVitaliProperty contract text in project/GMT/Ch01/Contract.lean and Submission.lean; no good-centre, dual-skeleton or bad-set lemma)`
- `rg -n 'DeformationTheorem|main_theorem' SNAPSHOT/project/GMT/Ch06/Contract.lean (def DeformationTheorem at line 274; main_theorem at line 362 has no proof; separate unproved Ch06 specification, not imported by Ch07)`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement' SNAPSHOT/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean (line 59)`
- `rg -n 'theorem volume_pi_ball|theorem volume_pi_Ioo' SNAPSHOT/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean (lines 272, 244)`
- `rg -n 'theorem volume_preserving_piEquivPiSubtypeProd|theorem volume_measurePreserving_piCongrLeft' SNAPSHOT/mathlib/Mathlib (Constructions/Pi.lean lines 726, 740)`
- `rg -n 'theorem prod_prod' SNAPSHOT/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean (line 231, arbitrary sets); rg -n 'theorem volume_eq_prod' (Prod.lean line 177)`
- `rg -n 'volume_preserving_symm_measurableEquiv_toLp' SNAPSHOT/mathlib/Mathlib (Measure/Haar/InnerProductSpace.lean line 124)`
- `rg -n 'theorem infDist_lt_iff' SNAPSHOT/mathlib/Mathlib (Topology/MetricSpace/HausdorffDistance.lean line 513)`
- `rg -n 'theorem _root_.Set.PairwiseDisjoint.countable_of_isOpen' SNAPSHOT/mathlib/Mathlib (Topology/Bases.lean line 487)`
- `rg -n 'theorem le_map_apply|theorem measure_preimage_equiv|theorem measure_biUnion_le|theorem measure_iUnion_fintype_le|theorem measure_biUnion' SNAPSHOT/mathlib/Mathlib (Measure/Map.lean 218, Dynamics/Ergodic/MeasurePreserving.lean 155, OuterMeasure/Basic.lean 74 and 84, Measure/Basic.lean 132)`
- `rg -n 'theorem EuclideanSpace.dist_eq' Analysis/InnerProductSpace/PiL2.lean (158); 'lemma exists_subset_card_eq' Data/Finset/Card.lean (677); 'lemma dist_pi_lt_iff' Topology/MetricSpace/Pseudo/Pi.lean (67); 'theorem orderEmbOfFin_mem' Data/Finset/Sort.lean (211); 'def ofInjective' Logic/Equiv/Set.lean (543); sum_le_sum_of_subset_of_nonneg (used in Algebra/Module/ZLattice/Summable.lean 191)`
- `grep -n of book/chapter-06.txt for the notation (lines 1405–1424), the dual-skeleton notation before 5.4 (1482–1490), display (2) of the proof of 5.4 (1524), and the proof of 5.1 displays (1)–(7) (1651–1721), with sed -n 1640,1730p and 1685,1706p`
- `python3 scans of RUN/dag.json (1598 nodes at the first scan, 1633 at the re-scan after review): selected node (depth 4, decomposing, attempt 1, no children); twin nodes with the identical lean_statement (cmcdt_good_center, waiting-children with children cmcdt_gc_tube_cover/bad_set_volume/cube_selection, all decomposing; dor_lmb_fcd_good_center, decomposing); proposed names dimred_mbl_dt_gc_{tube_cover,bad_set_volume,cube_selection} unreserved`
- `python3 reads of the twin's decomposition-v2.json, decomposition-audit-v1.json, decomposition-audit-v2.json and decomposition-review-receipt-v2.json, and of its three children's decomposition-v1.json and decomposition-audit-v1.json. All three children have should_split = false, and their audits are acceptable with required_changes []. Their earlier decomposition-review-retry.json files, read at the start of this session, have since been consumed by the runtime.`
- `for each swarm worktree: grep -l dimred_mbl_dt_gc_ workspaces/.swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean (no match); git log --all --oneline -S dimred_mbl_dt_gc_ -- GMT/Ch07/Submission.lean over 6993 refs (no match)`
- `python3 contract_scope() from verifier/gmt-compare.py on GMT/Ch07/Contract.lean with root GMT.Ch07.main_theorem (open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end); CHILD_TARGET = HumanizeNodeComparator.target`
- `python3 validate_lean_statement from /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py and verifier/lean_contract.py on the three child types and the parent type (all accepted unchanged)`
- `lake env lean /tmp/dimred-gc-verify-7f3a/chal/Challenge_{tube_cover,bad_set_volume,cube_selection,parent}.lean (EXIT 0, only the stub-proof warning); lake env lean /tmp/dimred-gc-verify-7f3a/lean/{AssemblyStub,Final,FinalOpenReal,InstCheck}.lean (EXIT 0; Final: no warnings, #print axioms propext, Classical.choice, Quot.sound for all eight declarations)`
- `grep -n '_existing_lean_name_problem' -A 45 /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py. An unaccepted node owned by another parent cannot be shared and needs a fresh name. A name may be shared only with an accepted node of identical type.`
- `independent read-only review subagent over /tmp/dimred-gc-verify-7f3a/decomposition.json, the supplied proof, the book text (chapter-06.txt and chapter-01.txt lines 612–623 for covering lemma 3.4) and the compiled Lean. It found no blocking issue, and its seven wording or provenance remarks are addressed in this version.`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch01/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Logic/Equiv/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9b0e7b29a0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9b0e7b29a0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/decomposition-review-receipt-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-goo-403169ba87/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-goo-403169ba87/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-goo-56178b7ea0/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-goo-56178b7ea0/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-goo-fce6a6fcb7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-goo-fce6a6fcb7/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dimred-gc-verify-7f3a/lean/Final2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/tmp/dimred-gc-verify-7f3a/chal/Challenge_tube_cover.lean`
- `/tmp/dimred-gc-verify-7f3a/chal/Challenge_bad_set_volume.lean`
- `/tmp/dimred-gc-verify-7f3a/chal/Challenge_cube_selection.lean`
- `/tmp/dimred-gc-verify-7f3a/chal/Challenge_parent.lean`
- `/tmp/dimred-gc-verify-7f3a/lean/AssemblyStub.lean`
- `/tmp/dimred-gc-verify-7f3a/lean/Final.lean`
- `/tmp/dimred-gc-verify-7f3a/lean/FinalOpenReal.lean`
- `/tmp/dimred-gc-verify-7f3a/lean/InstCheck.lean`

The pins match: project b4d606db, Mathlib 25730c7c, SimonGMT 2b366308. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot's frozen Ch07 contract. Neither the snapshot project nor Mathlib contains a good-centre, dual-skeleton or periodic bad-set lemma. The project's only Vitali material is the Ch01 contract definition HasSymmetricVitaliProperty, and its Ch06 DeformationTheorem is an unproved specification (its main_theorem has no proof) that Ch07 does not import. All three obligations are therefore new. Mathlib does provide every tool the child proofs cite, and all of them were found at the listed lines: the Vitali covering lemma, the cube and box volumes, measure preservation of the coordinate splitting, prod_prod for arbitrary sets, le_map_apply, infDist_lt_iff and countability of disjoint open families. The three child types are the audited types of the twin node cmcdt_good_center (identical frozen type), whose three children were each judged atomic with accepted audits. They are frozen here under globally unique names, as the runtime's collision rule requires for unaccepted nodes owned by another parent. Each elaborates in the comparator's challenge form and passes both validators. The exact appendix proofs and the assembly of the exact parent type compile against the pinned workspace with only propext, Classical.choice and Quot.sound.
