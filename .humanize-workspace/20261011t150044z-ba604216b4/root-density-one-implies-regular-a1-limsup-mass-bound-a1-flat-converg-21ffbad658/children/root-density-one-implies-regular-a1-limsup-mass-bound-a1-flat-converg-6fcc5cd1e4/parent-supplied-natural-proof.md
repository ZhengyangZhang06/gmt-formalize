# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.good_center-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.good_center-a1.bad_set_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to Geometric Measure Theory, Ch. 6, proof of the Deformation Theorem 5.1 (book/chapter-06.txt lines 1651–1691): the definition (1) of the good set G_j, the claim (2) that the bad set B_j has small L^{n+1}-measure, display (3), the 5-times Covering Lemma (Ch. 1, 3.4, book/chapter-01.txt lines 612–623) giving (4), and the summation after (4), which uses that the sets p_j^{-1}(B_{s_l}(b_l + z)) are pairwise disjoint. Simon's radii are written s, s_l here because ρ denotes the measure. This is step 2 ("Bad sets have small measure") of the supplied proof of the good-centre lemma Submission.dor_lmb_fcd_good_center, for one measure, applied there to the image measure ρ = p_J#ν on the coordinate plane S_J ≅ ℝ^d (d = n + 1 = m + 2), so that ρ(ℝ^d) = ν(ℝ^P) and ρ(O_r(p_J(a))) = ν(⋃_{z∈Z_J} p_J^{-1}(B_r(p_J(a) + z))).

Departures from the printed text and from step 2 of the supplied proof. None of them changes the covering-and-packing argument, which is Simon's:
(i) The covering balls are balls of Mathlib's sup metric on ℝ^d = Fin d → ℝ, i.e. open cubes of volume (2r)^d. They contain the Euclidean balls of the same radius. Simon and the supplied proof use Euclidean balls B_s(b) ⊂ S_j, of volume ω_{n+1}s^{n+1}. Simon's covering lemma 3.4 is stated for families of closed balls of bounded diameter in an arbitrary metric space. Step 4 uses Mathlib's version (Vitali.exists_disjoint_subfamily_covering_enlargement), which holds for any family of sets with bounded radii, so it applies to these open sup-metric balls. The periodic sets O_r(g) are still unions of Euclidean balls, as in (1).
(ii) The centres range over the open cube (1/4, 3/4)^d, i.e. |g_k − 1/2| < 1/4 for all k, instead of F_j ∩ B_{1/4}(x_j) (supplied proof: |g − x_J| < 1/4). This is the condition the selected node needs, since its centre a only satisfies |a_i − 1/2| < 1/4 for every i.
(iii) The radii range over (0, 1/4] instead of the open range (0, 1/4) of step 2 of the supplied proof. The text extraction of printed (1) and (3) loses the brackets, so the printed endpoint cannot be read off; (0, 1/4] contains either reading. This only enlarges the bad set, so the estimate is stronger. The disjointness step still works: the centres lie in the open cube, which gives the needed strict inequalities (step 7). With this range a good centre satisfies the bound at r = 1/4 as well, so the selected node does not need the continuity-from-below argument of step 5 of the supplied proof.
(iv) Only the centres g ∈ Bad have to be covered, not the whole balls. Lemma 3.4 (*) gives that the balls meet and r_g ≤ 2 r_b (Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement with τ = 2). For the centres alone this gives Bad ⊆ ⋃_b ball(b, 3 r_b) (step 6). Printed (4) and the supplied step 2 use the factor 5, which covers the whole balls. With cube volumes (2r)^d the printed bound 5^{n+1}ω_{n+1}/β becomes 6^d/β ≤ 10^d/β.
(v) M(T) (supplied: ν(ℝ^P)) is replaced by ρ(ℝ^d).
(vi) As in the supplied step 2, which bounds the outer measure, the bad set never has to be measurable. Only monotonicity and countable subadditivity of the outer measure volume are used.

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
 Here (6 r_b)^d = (6^d/β)(β r_b^d) because β > 0, and ofReal(st) = ofReal(s) ofReal(t) for s, t ≥ 0. This is the claim. (For d = 0 the same argument applies verbatim.) ∎

Appendix (supplementary, machine-checked; not needed for the argument above). The following Lean 4 declaration, placed in GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` after the contract's closing `end` of the noncomputable section (so with the contract's `open`s), follows the numbered steps above and adds no helper declaration. It was compiled with `lake env lean` against the pinned workspace (Lean v4.35.0-rc3, Mathlib 25730c7c), alone and inserted into a copy of GMT/Ch07/Submission.lean; `#print axioms` reports only propext, Classical.choice, Quot.sound.

/-- **Simon, Ch. 6, proof of 5.1** ((1)–(4) and the summation after them: the bad set of centres
is small).  Let `ρ` be a finite measure on `ℝᵈ` and `β > 0`.  Call a centre `g` of the open cube
`(1/4, 3/4)ᵈ` bad if `β rᵈ ρ(ℝᵈ) < ρ(O_r(g))` for some `r ∈ (0, 1/4]`, where
`O_r(g) = {y : |y − g − z| < r for some z ∈ ℤᵈ}` is the open `r`-neighbourhood of `g + ℤᵈ`.  Then
the bad set has Lebesgue measure at most `10ᵈ/β`.  Vitali's covering lemma gives bad centres `b`
with pairwise disjoint sup-metric balls `B(b, r_b)` such that the balls `B(b, 3r_b)` cover the bad
set.  The sets `O_{r_b}(b)` are then pairwise disjoint as well, so `Σ_b β r_bᵈ ≤ 1`, and the
bad set has measure at most `Σ_b (6r_b)ᵈ ≤ 6ᵈ/β`. -/
theorem Submission.dor_lmb_fcd_gc_bad_set_volume : ∀ (d : ℕ) (ρ : Measure (Fin d → ℝ)), IsFiniteMeasure ρ → ∀ β : ℝ, 0 < β → volume {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ENNReal.ofReal (β * r ^ d) * ρ univ < ρ {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}} ≤ ENNReal.ofReal (10 ^ d / β) := by
  classical
  intro d ρ hρ β hβ
  set O : (Fin d → ℝ) → ℝ → Set (Fin d → ℝ) := fun g r =>
    {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} with hO
  set Bad := {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r)}
  -- step 1: the periodic sets `O_r(g)` are open
  have hOopen : ∀ g r, IsOpen (O g r) := by
    intro g r
    have : O g r = ⋃ z : Fin d → ℤ, {y | ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} := by
      ext y; simp [hO]
    rw [this]
    exact isOpen_iUnion fun z => isOpen_lt (by fun_prop) continuous_const
  -- step 2: if `ρ(ℝᵈ) = 0` the bad set is empty
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
  -- step 3: a radius `r_g` for every bad centre `g`
  have hrad : ∀ g ∈ Bad, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r) := fun g hg => hg.2
  choose! rad hrad0 hrad1 hradlt using hrad
  -- step 4: Vitali's covering lemma for the balls `B(g, r_g)`, with `τ = 2`
  obtain ⟨u, huBad, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun g => ball g (rad g)) Bad rad 2 one_lt_two (fun g hg => (hrad0 g hg).le) (1 / 4) hrad1
    (fun g hg => ⟨g, mem_ball_self (hrad0 g hg)⟩)
  -- step 5: `u` is countable
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun g hg => ⟨g, mem_ball_self (hrad0 g (huBad hg))⟩)
  -- step 6: the balls `B(b, 3 r_b)`, `b ∈ u`, cover the bad set
  have hBadsub : Bad ⊆ ⋃ b ∈ u, ball b (3 * rad b) := by
    intro g hg
    obtain ⟨b, hbu, ⟨y, hy1, hy2⟩, hle⟩ := hucov g hg
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hy1 hy2 ⊢
    calc dist g b ≤ dist g y + dist y b := dist_triangle _ _ _
      _ < rad g + rad b := by rw [dist_comm g y]; exact add_lt_add hy1 hy2
      _ ≤ 3 * rad b := by linarith
  -- step 7: the periodic sets `O_{r_b}(b)`, `b ∈ u`, are pairwise disjoint
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
    -- the centres lie in `(1/4, 3/4)ᵈ` and the radii are `≤ 1/4`, so the integer shifts agree
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
    -- then `y − z` lies in both balls `B(b, r_b)` and `B(b', r_{b'})`
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
  -- step 8: `S = Σ_{b ∈ u} β r_bᵈ ≤ 1`
  set S : ℝ≥0∞ := ∑' b : u, ENNReal.ofReal (β * rad b ^ d)
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
  -- step 9: the volume estimate
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
2. Vitali (Vitali.exists_disjoint_subfamily_covering_enlargement, τ = 2) on the sup-metric balls ball(g, r_g) gives a pairwise disjoint subfamily ball(b, r_b), b ∈ u, countable by separability, with Bad ⊆ ⋃_{b∈u} ball(b, 3 r_b) (printed (4), factor 3 for centres).
3. For b ≠ b' in u the periodic sets O_{r_b}(b) and O_{r_{b'}}(b') are disjoint: the centres lie in (1/4, 3/4)^d and the radii are ≤ 1/4, so a common point forces equal integer shifts, which reduces to the disjoint balls.
4. Summation: Σ_b β r_b^d ρ(ℝ^d) ≤ Σ_b ρ(O_{r_b}(b)) = ρ(⋃_b O_{r_b}(b)) ≤ ρ(ℝ^d), so Σ_b β r_b^d ≤ 1 after cancelling 0 < ρ(ℝ^d) < ∞.
5. volume(Bad) ≤ Σ_b volume(ball(b, 3 r_b)) = Σ_b (6 r_b)^d = (6^d/β) Σ_b β r_b^d ≤ 6^d/β ≤ 10^d/β.

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
