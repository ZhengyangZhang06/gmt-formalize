# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.bf_trichotomy-a1`
- Child DAG node: `root.rectifiability-a1.bf_trichotomy-a1.slice_density_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent-supplied proof of rectifiability_bf_trichotomy (P. Mattila, Geometry of Sets and Measures in Euclidean Spaces, Lemma 18.9; R. Hovila, E. Järvenpää, M. Järvenpää, F. Ledrappier, arXiv:1104.3453, Lemma 2.4). Along each affine slice c ↦ w ⊕_j c the Mickle–Radó theorem [Ma, 18.5] (sibling mickle_rado) applies, and Fubini extends the conclusion to almost every parameter. The parent's ψ_{j,u}(B(0,t))/tᵏ is written here as sup_{0<r<δ} μ(B(a,r) ∩ K_{j,u}(t))/(rt)ᵏ; step 7 converts between the two. The parent's Fubini over W_j × ℝᵏ is carried out in the equivalent form of step 9, which needs no coordinate splitting.

Notation. c(x) := ENNReal.ofReal x. B(·,·) denotes open balls. Write ⊕ for ⊕_j. For y ∈ ℝ^N, y_j := ⟨e_j,y⟩. For w ∈ (ℝ^N)^k and C ⊆ ℝᵏ let K_w(C) := {x ∈ ℝ^N : x ≠ a, ∃ c ∈ C, L_{w⊕c}(x − a) = 0}, so that K_{j,u}(t) = K_u(B(0,t)). Let 𝔅_j := {u : (T3) fails at u, 0 < ϑ_j(u) < ∞}.

1. Algebra.
 (a) L_{w⊕c}(y) = L_w(y) + y_j·c: the i-th coordinate is ⟨w_i + c_ie_j, y⟩ = ⟨w_i,y⟩ + c_iy_j (EuclideanSpace.inner_single_left).
 (b) (w⊕c)⊕c′ = w⊕(c + c′): coordinatewise, (w_i + c_ie_j) + c′_ie_j = w_i + (c_i + c′_i)e_j.
 (c) L_w x − L_w a = L_w(x − a). So (T3) at w is equivalent to: ∃ x ∈ E with x ≠ a, |x − a| < δ and L_w(x − a) = 0.
 (d) K_w(⋃_i C_i) = ⋃_i K_w(C_i); K_w is monotone in C; K_w(∅) = ∅.
 (e) Translation: K_w(B(c,t)) = K_{w⊕c}(B(0,t)) for all c ∈ ℝᵏ and t ∈ ℝ. Indeed c′ ∈ B(c,t) iff c″ := c′ − c ∈ B(0,t), and w⊕c′ = (w⊕c)⊕c″ by (b).
 (f) Explicit form: for t > 0, K_w(B(0,t)) = {x : |L_w(x − a)| < t|(x − a)_j|} ∪ {x : x ≠ a, (x − a)_j = 0, L_w(x − a) = 0}. Proof, with y := x − a:
  - If y_j ≠ 0: by (a), L_{w⊕c}(y) = 0 iff c = −L_w(y)/y_j, and then |c| < t iff |L_w(y)| < t|y_j|; also y_j ≠ 0 implies y ≠ 0.
  - If y_j = 0: L_{w⊕c}(y) = L_w(y), so x ∈ K_w(B(0,t)) iff y ≠ 0 and L_w(y) = 0 (take c = 0 ∈ B(0,t)). The first set contains no x with y_j = 0.
 Consequently the set {(u,x) : x ∈ K_u(B(0,t))} is Borel in (ℝ^N)^k × ℝ^N: it is empty for t ≤ 0, and for t > 0 it is given by (f) through continuous functions of (u,x). This joint form is the one used in step 8. Steps 3 and 7 use continuity from below, which needs no measurability.

2. The outer measure ψ_w. Fix w ∈ (ℝ^N)^k and define, for C ⊆ ℝᵏ, ψ_w(C) := sup_{r∈(0,δ)} μ(B(a,r) ∩ K_w(C))/c(rᵏ). Then ψ_w is an outer measure on ℝᵏ:
 - ψ_w(∅) = 0 by (d);
 - ψ_w is monotone by (d) and monotonicity of μ;
 - ψ_w is countably subadditive. For C = ⋃_n C_n and r ∈ (0,δ), μ(B(a,r) ∩ K_w(C)) = μ(⋃_n (B(a,r) ∩ K_w(C_n))) ≤ Σ_n μ(B(a,r) ∩ K_w(C_n)) (measure_iUnion_le). Dividing by c(rᵏ), i.e. multiplying by the constant c(rᵏ)⁻¹ (ENNReal.tsum_mul_right), gives μ(B(a,r) ∩ K_w(C))/c(rᵏ) ≤ Σ_n μ(B(a,r) ∩ K_w(C_n))/c(rᵏ) ≤ Σ_n ψ_w(C_n). Then take the sup over r.
 In Lean, build it with OuterMeasure.mk and measureOf := ψ_w; its last field only requires subadditivity for pairwise disjoint sequences, which is implied.

3. Ball continuity: ψ_w(B(c,τ)) = sup_{τ′∈(0,τ)} ψ_w(B(c,τ′)) for all c ∈ ℝᵏ and τ ∈ ℝ.
 - If τ ≤ 0, both sides are 0: B(c,τ) = ∅ and the index set is empty.
 - Let τ > 0 and τ_n := τ(1 − 1/(n+2)) ↑ τ. Every τ′ < τ is below some τ_n, so B(c,τ) = ⋃_n B(c,τ_n) is an increasing union. By (d), K_w(B(c,τ)) = ⋃_n K_w(B(c,τ_n)), also increasing.
 - For each r, continuity from below (Monotone.measure_iUnion or Directed.measure_iUnion; no measurability needed) gives μ(B(a,r) ∩ K_w(B(c,τ))) = sup_n μ(B(a,r) ∩ K_w(B(c,τ_n))) ≤ sup_{τ′∈(0,τ)} μ(B(a,r) ∩ K_w(B(c,τ′))).
 - Divide by c(rᵏ) (ENNReal.iSup_div) and exchange the two suprema to get ψ_w(B(c,τ)) ≤ sup_{τ′∈(0,τ)} ψ_w(B(c,τ′)). The reverse inequality is monotonicity.

4. D_w := {c ∈ ℝᵏ : (T3) fails at w⊕c} is Borel. Let 𝒲 := {(a′,v) ∈ ℝ^N × (ℝ^N)^k : ∃ x ∈ E, x ≠ a′, |x − a′| < δ, L_vx = L_va′}. The sibling witness_set_measurable shows 𝒲 is measurable, since E is σ-compact. The map c ↦ (a, w⊕c) is continuous (affine), hence measurable, and D_w is the preimage of the complement of 𝒲 under it.

5. ψ_w(D_w) = 0. Let r ∈ (0,δ) and suppose x ∈ E ∩ B(a,r) ∩ K_w(D_w). Then x ≠ a, and L_{w⊕c}(x − a) = 0 for some c ∈ D_w. As |x − a| < r < δ, by 1(c) x witnesses (T3) at w⊕c, contradicting c ∈ D_w. Hence B(a,r) ∩ K_w(D_w) ⊆ ℝ^N ∖ E, so μ(B(a,r) ∩ K_w(D_w)) ≤ μ(ℝ^N ∖ E) = 0. Every term of the supremum defining ψ_w(D_w) is therefore 0.

6. Mickle–Radó. Steps 2–5 give the hypotheses of the sibling mickle_rado (Submission.rectifiability_mickle_rado) for ψ := ψ_w and D := D_w: an outer measure with ball continuity, D Borel, and ψ(D) = 0. It yields Lebesgue-measure zero for {c ∈ D_w : 0 < ϑ̃_w(c) < ∞}, where ϑ̃_w(c) := limsup_{t→0⁺} ψ_w(B(c,t))/c(tᵏ).

7. Identification: ϑ̃_w(c) = ϑ_j(w⊕c) for every c. For t > 0,
 ψ_w(B(c,t))/c(tᵏ) = sup_{r∈(0,δ)} μ(B(a,r) ∩ K_w(B(c,t)))/c(rᵏ)/c(tᵏ)   (ENNReal.iSup_div)
  = sup_{r∈(0,δ)} μ(B(a,r) ∩ K_{w⊕c}(B(0,t)))/c((rt)ᵏ).
 The second equality uses 1(e) and c(rᵏ)·c(tᵏ) = c((rt)ᵏ) with both factors in (0,∞), so that x/c(rᵏ)/c(tᵏ) = x/c((rt)ᵏ). The right side is the function whose limsup is ϑ_j(w⊕c). The two functions of t agree on (0,∞) ∈ 𝓝[>]0, so their limsups agree (Filter.limsup_congr).
 Now w⊕c ∈ 𝔅_j iff (T3) fails at w⊕c and 0 < ϑ_j(w⊕c) < ∞, i.e. iff c ∈ D_w and 0 < ϑ̃_w(c) < ∞. So by step 6, for every w ∈ (ℝ^N)^k: Lebesgue measure of {c ∈ ℝᵏ : w⊕c ∈ 𝔅_j} is 0.

8. 𝔅_j is measurable.
 (a) u ↦ ϑ_j(u) is measurable. Apply the sibling limsup_sup_measurable with Z := (ℝ^N)^k, Y := ℝ^N, exponent k, the measure μ, δ, and G(r,t) := {(u,x) : x ∈ B(a,r) ∩ K_u(B(0,t))}. Then {x : (u,x) ∈ G(r,t)} = B(a,r) ∩ K_{j,u}(t), and the function in that lemma is u ↦ ϑ_j(u). Its hypotheses hold:
  - G(r,t) is measurable: {(u,x) : |x − a| < r} is open, and {(u,x) : x ∈ K_u(B(0,t))} is Borel by 1(f); (ℝ^N)^k × ℝ^N is second countable, so Borel and product σ-algebras agree.
  - G is monotone in t, since B(0,t) ⊆ B(0,t′) for t ≤ t′ and K_u is monotone.
  - For r > 0, G(r,t) = ⋃_{r′∈(0,r)} G(r′,t), because B(a,r) = ⋃_{r′∈(0,r)} B(a,r′) (given |x − a| < r take r′ := (|x − a| + r)/2).
 (b) {u : (T3) fails at u} is the preimage of the complement of 𝒲 (step 4) under the continuous map u ↦ (a,u).
 (c) Hence 𝔅_j = {u : (T3) fails at u} ∩ ϑ_j⁻¹((0,∞)) is measurable.

9. Fubini over the slices.
 - Let e(c) := (c₁e_j, …, c_ke_j) ∈ (ℝ^N)^k and Ψ(w,c) := w⊕c = w + e(c) on (ℝ^N)^k × ℝᵏ. Ψ is continuous, so P := Ψ⁻¹(𝔅_j) is measurable.
 - Let 𝓛 be Lebesgue measure on (ℝ^N)^k: the volume on Fin k → Eucl N, an additive Haar measure, hence translation invariant and σ-finite. Let 𝓛_k be Lebesgue measure on ℝᵏ; it is σ-finite with 𝓛_k(ℝᵏ) = ∞ since k ≥ 1 (measure_univ_of_isAddLeftInvariant).
 - Tonelli (Measure.prod_apply): (𝓛 ⊗ 𝓛_k)(P) = ∫ 𝓛_k({c : w⊕c ∈ 𝔅_j}) d𝓛(w) = 0, by step 7.
 - Tonelli in the other order (Measure.prod_apply_symm): (𝓛 ⊗ 𝓛_k)(P) = ∫ 𝓛({w : w + e(c) ∈ 𝔅_j}) d𝓛_k(c) = ∫ 𝓛(𝔅_j) d𝓛_k(c) = 𝓛(𝔅_j)·𝓛_k(ℝᵏ) = 𝓛(𝔅_j)·∞. This uses translation invariance 𝓛((· + e(c))⁻¹(𝔅_j)) = 𝓛(𝔅_j) (measure_preimage_add_right).
 - Hence 𝓛(𝔅_j)·∞ = 0, which forces 𝓛(𝔅_j) = 0. ∎

Lean reference proof (appendix; written by the independent Lean reviewer of this decomposition and re-compiled by the author). It is compile-checked as a single declaration against the exact frozen statement inside `namespace GMT.Ch06` of a scratch copy of the frozen project (commit d8d46c9587747dee0751a1f780fcafdba16a3886, Lean v4.35.0-rc3, pinned Mathlib 25730c7c), with its declared sibling dependencies Submission.rectifiability_mickle_rado, Submission.rectifiability_bf_limsup_sup_measurable, Submission.rectifiability_bf_witness_set_measurable present as theorems of their exact frozen types; with those siblings proved, #print axioms = [propext, Classical.choice, Quot.sound]. It introduces no auxiliary declarations.
```lean
theorem Submission.rectifiability_bf_slice_density_null : (∀ (N m : ℕ) (μ : Measure (Eucl N)) (E : Set (Eucl N)) (δ : ℝ) (a : Eucl N) (j : Fin N), SFinite μ → IsSigmaCompact E → μ Eᶜ = 0 → (volume : Measure (Fin (m + 1) → Eucl N)) {u : Fin (m + 1) → Eucl N | ¬ (∃ x ∈ E, x ≠ a ∧ dist x a < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) a) : Eucl (m + 1))) ∧ 0 < limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) ∧ limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) < ⊤} = 0) := by
  intro N m μ E δ a j hμ hE hEc
  let e : Eucl N := EuclideanSpace.single j (1 : ℝ)
  let Lu : (Fin (m + 1) → Eucl N) → Eucl N → Eucl (m + 1) := fun u y =>
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) y) : Eucl (m + 1))
  let T3 : (Fin (m + 1) → Eucl N) → Prop := fun u => ∃ x ∈ E, x ≠ a ∧ dist x a < δ ∧
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) x) : Eucl (m + 1)) =
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) a) : Eucl (m + 1))
  let Ks : (Fin (m + 1) → Eucl N) → ℝ → Set (Eucl N) := fun u t => {x | x ≠ a ∧
    ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) =>
      inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}
  let θ : (Fin (m + 1) → Eucl N) → ℝ≥0∞ := fun u => limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ,
    μ (ball a r ∩ Ks u t) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0)
  let B : Set (Fin (m + 1) → Eucl N) := {u | ¬ T3 u ∧ 0 < θ u ∧ θ u < ⊤}
  show (volume : Measure (Fin (m + 1) → Eucl N)) B = 0
  -- algebra
  have hfib : ∀ (u : Fin (m + 1) → Eucl N) (c : Eucl (m + 1)) (y : Eucl N),
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) y) :
        Eucl (m + 1)) = Lu u y + (y j) • c := by
    intro u c y
    ext i
    simp [Lu, inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left, mul_comm]
  have hLsub : ∀ (v : Fin (m + 1) → Eucl N) (x y : Eucl N), Lu v (x - y) = Lu v x - Lu v y := by
    intro v x y
    ext i
    simp [Lu, inner_sub_right]
  -- explicit form of the fibre union
  have hKs : ∀ u t, 0 < t → Ks u t = {x | ‖Lu u (x - a)‖ < t * ‖(x - a) j‖} ∪
      {x | x ≠ a ∧ (x - a) j = 0 ∧ Lu u (x - a) = 0} := by
    intro u t ht
    ext x
    simp only [Ks, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨hxa, c, hc, h0⟩
      rw [hfib] at h0
      by_cases hyj : (x - a) j = 0
      · right
        refine ⟨hxa, hyj, ?_⟩
        rw [hyj, zero_smul, add_zero] at h0
        exact h0
      · left
        have hL : Lu u (x - a) = -((x - a) j • c) := eq_neg_of_add_eq_zero_left h0
        rw [hL, norm_neg, norm_smul]
        have hc' : ‖c‖ < t := mem_ball_zero_iff.1 hc
        have hpos : 0 < ‖(x - a) j‖ := norm_pos_iff.2 hyj
        calc ‖(x - a) j‖ * ‖c‖ < ‖(x - a) j‖ * t := mul_lt_mul_of_pos_left hc' hpos
          _ = t * ‖(x - a) j‖ := mul_comm _ _
    · rintro (h | ⟨hxa, hyj, h0⟩)
      · have hyj : (x - a) j ≠ 0 := by
          intro h'
          rw [h', norm_zero, mul_zero] at h
          exact (norm_nonneg _).not_gt h
        have hxa : x ≠ a := by
          intro h'
          apply hyj
          rw [h', sub_self]
          rfl
        refine ⟨hxa, (-((x - a) j)⁻¹) • Lu u (x - a), ?_, ?_⟩
        · rw [mem_ball_zero_iff, norm_smul, norm_neg, norm_inv, inv_mul_lt_iff₀ (norm_pos_iff.2 hyj)]
          linarith [h]
        · rw [hfib, smul_smul, mul_neg, mul_inv_cancel₀ hyj, neg_smul, one_smul, add_neg_cancel]
      · refine ⟨hxa, 0, mem_ball_self ht, ?_⟩
        rw [hfib, smul_zero, add_zero]
        exact h0
  -- θ is measurable
  let G : ℝ → ℝ → Set ((Fin (m + 1) → Eucl N) × Eucl N) := fun r t => {q | q.2 ∈ ball a r ∩ Ks q.1 t}
  have hc1 : Continuous fun q : (Fin (m + 1) → Eucl N) × Eucl N => Lu q.1 (q.2 - a) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp continuous_fst).inner (continuous_snd.sub continuous_const)
  have hc2 : Continuous fun q : (Fin (m + 1) → Eucl N) × Eucl N => (q.2 - a) j :=
    (PiLp.continuous_apply 2 _ j).comp (continuous_snd.sub continuous_const)
  have hGm : ∀ r t, MeasurableSet (G r t) := by
    intro r t
    rcases le_or_gt t 0 with ht | ht
    · have : G r t = ∅ := by
        ext q
        simp only [G, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨-, -, c, hc, -⟩
        rw [ball_eq_empty.2 ht] at hc
        exact hc
      rw [this]
      exact MeasurableSet.empty
    · have : G r t = {q | dist q.2 a < r} ∩ ({q | ‖Lu q.1 (q.2 - a)‖ < t * ‖(q.2 - a) j‖} ∪
          ({q | q.2 ≠ a} ∩ {q | (q.2 - a) j = 0} ∩ {q | Lu q.1 (q.2 - a) = 0})) := by
        ext q
        simp only [G, mem_ofPred_eq, mem_inter_iff, mem_ball]
        rw [hKs q.1 t ht]
        simp only [mem_union, mem_ofPred_eq, mem_inter_iff, and_assoc]
      rw [this]
      refine (isOpen_lt (continuous_snd.dist continuous_const) continuous_const).measurableSet.inter
        (MeasurableSet.union ?_ ?_)
      · exact (isOpen_lt hc1.norm (continuous_const.mul hc2.norm)).measurableSet
      · exact ((isOpen_ne_fun continuous_snd continuous_const).measurableSet.inter
          (isClosed_eq hc2 continuous_const).measurableSet).inter
          (isClosed_eq hc1 continuous_const).measurableSet
  have hGmono : ∀ r t t', t ≤ t' → G r t ⊆ G r t' := by
    rintro r t t' htt' q ⟨hq1, hxa, c, hc, h0⟩
    exact ⟨hq1, hxa, c, ball_subset_ball htt' hc, h0⟩
  have hGcont : ∀ r t, 0 < r → G r t = ⋃ r' ∈ Ioo (0 : ℝ) r, G r' t := by
    intro r t hr
    ext q
    simp only [G, mem_iUnion, mem_ofPred_eq, mem_inter_iff, mem_ball, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(dist q.2 a + r) / 2, ⟨by positivity, by linarith⟩, by linarith, h2⟩
    · rintro ⟨r', ⟨-, hr'r⟩, h1, h2⟩
      exact ⟨h1.trans hr'r, h2⟩
  have hθm : Measurable θ :=
    Submission.rectifiability_bf_limsup_sup_measurable (Fin (m + 1) → Eucl N) (Eucl N) (m + 1) μ δ G hμ hGm hGmono hGcont
  -- B is measurable
  have hW := Submission.rectifiability_bf_witness_set_measurable N m E δ hE
  have hT3m : MeasurableSet {u : Fin (m + 1) → Eucl N | ¬ T3 u} :=
    (measurable_const.prodMk measurable_id) hW.compl
  have hBm : MeasurableSet B :=
    hT3m.inter ((measurableSet_lt measurable_const hθm).inter (measurableSet_lt hθm measurable_const))
  -- slices
  let sh : Eucl (m + 1) → (Fin (m + 1) → Eucl N) := fun c i => c i • EuclideanSpace.single j (1 : ℝ)
  have hsh : Continuous sh := continuous_pi fun i => (PiLp.continuous_apply 2 _ i).smul continuous_const
  have hslice : ∀ w : Fin (m + 1) → Eucl N, (volume : Measure (Eucl (m + 1))) {c | w + sh c ∈ B} = 0 := by
    intro w
    let KC : Set (Eucl (m + 1)) → Set (Eucl N) := fun C => {x | x ≠ a ∧ ∃ c ∈ C,
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (w i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) :
        Eucl (m + 1)) = 0}
    have hKCmono : ∀ C₁ C₂, C₁ ⊆ C₂ → KC C₁ ⊆ KC C₂ := by
      rintro C₁ C₂ h x ⟨hxa, c, hc, h0⟩
      exact ⟨hxa, c, h hc, h0⟩
    have hKCunion : ∀ (s : ℕ → Set (Eucl (m + 1))), KC (⋃ i, s i) = ⋃ i, KC (s i) := by
      intro s
      ext x
      simp only [KC, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxa, c, ⟨i, hci⟩, h0⟩
        exact ⟨i, hxa, c, hci, h0⟩
      · rintro ⟨i, hxa, c, hci, h0⟩
        exact ⟨hxa, c, ⟨i, hci⟩, h0⟩
    let ψ : OuterMeasure (Eucl (m + 1)) :=
      { measureOf := fun C => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ KC C) / ENNReal.ofReal (r ^ (m + 1))
        empty := by
          have : KC ∅ = ∅ := by
            ext x
            simp [KC]
          simp [this]
        mono := fun {s₁ s₂} h => iSup₂_mono fun r _ =>
          ENNReal.div_le_div_right (measure_mono (inter_subset_inter_right _ (hKCmono _ _ h))) _
        iUnion_nat := fun s _ => by
          refine iSup₂_le fun r hr => ?_
          rw [hKCunion, inter_iUnion]
          calc μ (⋃ i, ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1))
              ≤ (∑' i, μ (ball a r ∩ KC (s i))) / ENNReal.ofReal (r ^ (m + 1)) :=
                ENNReal.div_le_div_right (measure_iUnion_le _) _
            _ = ∑' i, μ (ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1)) := by
                simp only [div_eq_mul_inv, ENNReal.tsum_mul_right]
            _ ≤ ∑' i, ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1)) :=
                ENNReal.tsum_le_tsum fun i => le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
                  μ (ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1))) r hr }
    have hψ : ∀ C, ψ C = ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ KC C) / ENNReal.ofReal (r ^ (m + 1)) :=
      fun C => rfl
    -- ball continuity
    have hball : ∀ (c : Eucl (m + 1)) (τ : ℝ), ψ (ball c τ) = ⨆ τ' ∈ Ioo (0 : ℝ) τ, ψ (ball c τ') := by
      intro c τ
      apply le_antisymm
      · rcases le_or_gt τ 0 with hτ | hτ
        · rw [ball_eq_empty.2 hτ, measure_empty]
          exact zero_le
        · rw [hψ]
          refine iSup₂_le fun r hr => ?_
          let τn : ℕ → ℝ := fun n => τ - τ / ((n : ℝ) + 2)
          have hτn_mono : Monotone τn := by
            intro n n' hnn'
            simp only [τn]
            have : τ / ((n' : ℝ) + 2) ≤ τ / ((n : ℝ) + 2) := by
              apply div_le_div_of_nonneg_left hτ.le (by positivity)
              have : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
              linarith
            linarith
          have hτn_mem : ∀ n, τn n ∈ Ioo 0 τ := by
            intro n
            have h1 : τ / ((n : ℝ) + 2) < τ := by
              rw [div_lt_iff₀ (by positivity)]
              have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
              nlinarith
            have h2 : 0 < τ / ((n : ℝ) + 2) := by positivity
            exact ⟨by simp only [τn]; linarith, by simp only [τn]; linarith⟩
          have hballU : ball c τ = ⋃ n, ball c (τn n) := by
            ext c'
            simp only [mem_ball, mem_iUnion]
            constructor
            · intro hd
              obtain ⟨n, hn⟩ := exists_nat_gt (τ / (τ - dist c' c))
              refine ⟨n, ?_⟩
              simp only [τn]
              have hpos : 0 < τ - dist c' c := by linarith
              have : τ / ((n : ℝ) + 2) < τ - dist c' c := by
                rw [div_lt_iff₀ (by positivity)]
                rw [div_lt_iff₀ hpos] at hn
                nlinarith
              linarith
            · rintro ⟨n, hn⟩
              exact hn.trans (hτn_mem n).2
          have hmono_sets : Monotone (fun n => ball a r ∩ KC (ball c (τn n))) := by
            intro n n' hnn'
            exact inter_subset_inter_right _ (hKCmono _ _ (ball_subset_ball (hτn_mono hnn')))
          have hmeas : μ (ball a r ∩ KC (ball c τ)) = ⨆ n, μ (ball a r ∩ KC (ball c (τn n))) := by
            rw [hballU, hKCunion, inter_iUnion]
            exact hmono_sets.measure_iUnion
          rw [hmeas, ENNReal.iSup_div]
          refine iSup_le fun n => ?_
          refine le_trans ?_ (le_iSup₂ (f := fun τ' (_ : τ' ∈ Ioo (0 : ℝ) τ) => ψ (ball c τ')) (τn n) (hτn_mem n))
          rw [hψ]
          exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
            μ (ball a r ∩ KC (ball c (τn n))) / ENNReal.ofReal (r ^ (m + 1))) r hr
      · exact iSup₂_le fun τ' hτ' => ψ.mono (ball_subset_ball hτ'.2.le)
    -- the slice parameters without a fibre witness
    let D : Set (Eucl (m + 1)) := {c | ¬ T3 (w + sh c)}
    have hDm : MeasurableSet D :=
      (measurable_const.prodMk (continuous_const.add hsh).measurable) hW.compl
    have hψD : ψ D = 0 := by
      rw [hψ]
      refine le_antisymm (iSup₂_le fun r hr => ?_) zero_le
      have : μ (ball a r ∩ KC D) = 0 := by
        refine measure_mono_null (fun x hx => ?_) hEc
        obtain ⟨hxr, hxa, c, hcD, hx0⟩ := hx
        intro hxE
        apply hcD
        refine ⟨x, hxE, hxa, (mem_ball.1 hxr).trans hr.2, ?_⟩
        have h0 : Lu (w + sh c) (x - a) = 0 := hx0
        rw [hLsub] at h0
        exact sub_eq_zero.1 h0
      rw [this, ENNReal.zero_div]
    have hMR := Submission.rectifiability_mickle_rado m ψ D hball hDm hψD
    -- translation identity
    have hKCtr : ∀ (c : Eucl (m + 1)) (t : ℝ), KC (ball c t) = Ks (w + sh c) t := by
      intro c t
      ext x
      simp only [KC, Ks, mem_ofPred_eq]
      constructor
      · rintro ⟨hxa, c', hc', h0⟩
        refine ⟨hxa, c' - c, ?_, ?_⟩
        · rw [mem_ball_zero_iff, ← mem_ball_iff_norm]
          exact hc'
        · have hv : ∀ i, (w + sh c) i + (c' - c) i • EuclideanSpace.single j (1 : ℝ) =
              w i + c' i • EuclideanSpace.single j (1 : ℝ) := by
            intro i
            simp only [sh, Pi.add_apply, PiLp.sub_apply, sub_smul]
            abel
          simp only [hv]
          exact h0
      · rintro ⟨hxa, c'', hc'', h0⟩
        refine ⟨hxa, c + c'', ?_, ?_⟩
        · rw [mem_ball_iff_norm, add_sub_cancel_left, ← mem_ball_zero_iff]
          exact hc''
        · have hv : ∀ i, w i + (c + c'') i • EuclideanSpace.single j (1 : ℝ) =
              (w + sh c) i + c'' i • EuclideanSpace.single j (1 : ℝ) := by
            intro i
            simp only [sh, Pi.add_apply, PiLp.add_apply, add_smul]
            abel
          simp only [hv]
          exact h0
    have hid : ∀ c : Eucl (m + 1), limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) =
        θ (w + sh c) := by
      intro c
      apply limsup_congr
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [hψ, ENNReal.iSup_div]
      refine iSup_congr fun r => ?_
      rw [ENNReal.iSup_div]
      refine iSup_congr fun hr => ?_
      rw [hKCtr c t]
      have hr0 : 0 < r := hr.1
      have hA0 : ENNReal.ofReal (r ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
        ← ENNReal.mul_inv (Or.inl hA0) (Or.inl ENNReal.ofReal_ne_top),
        ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    refine le_antisymm (le_trans (measure_mono ?_) hMR.le) zero_le
    intro c hc
    refine ⟨hc.1, ?_, ?_⟩
    · rw [hid c]; exact hc.2.1
    · rw [hid c]; exact hc.2.2
  -- Fubini
  have hP : MeasurableSet ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B) :=
    (continuous_fst.add (hsh.comp continuous_snd)).measurable hBm
  have h1 : ((volume : Measure (Fin (m + 1) → Eucl N)).prod (volume : Measure (Eucl (m + 1))))
      ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B) = 0 := by
    rw [Measure.prod_apply hP]
    have : ∀ w : Fin (m + 1) → Eucl N, (volume : Measure (Eucl (m + 1)))
        (Prod.mk w ⁻¹' ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B)) = 0 :=
      fun w => hslice w
    simp [this]
  have h2 : ((volume : Measure (Fin (m + 1) → Eucl N)).prod (volume : Measure (Eucl (m + 1))))
      ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B) =
        (volume : Measure (Fin (m + 1) → Eucl N)) B * ⊤ := by
    rw [Measure.prod_apply_symm hP]
    have : ∀ c : Eucl (m + 1), (volume : Measure (Fin (m + 1) → Eucl N))
        ((fun w => (w, c)) ⁻¹' ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B)) =
          (volume : Measure (Fin (m + 1) → Eucl N)) B :=
      fun c => measure_preimage_add_right (volume : Measure (Fin (m + 1) → Eucl N)) (sh c) B
    simp only [this]
    rw [lintegral_const, measure_univ_of_isAddLeftInvariant]
  rw [h1] at h2
  rcases mul_eq_zero.1 h2.symm with h | h
  · exact h
  · exact absurd h ENNReal.top_ne_zero
```

## Key steps

1. For fixed w, ψ_w(C) := sup_{0<r<δ} μ(B(a,r) ∩ K_w(C))/rᵏ is an outer measure on ℝᵏ and satisfies ψ_w(B(c,τ)) = sup_{τ′<τ} ψ_w(B(c,τ′)).
2. D_w := {c : (T3) fails at w⊕_jc} is Borel (witness_set_measurable), and ψ_w(D_w) = 0 because μ(ℝ^N∖E) = 0.
3. mickle_rado with the translation identity K_w(B(c,t)) = K_{w⊕_jc}(B(0,t)) gives Lᵏ{c : w⊕_jc ∈ 𝔅_j} = 0 for every w.
4. ϑ_j is Borel (limsup_sup_measurable), so 𝔅_j is Borel.
5. Tonelli on (ℝ^N)^k × ℝᵏ for (w,c) ↦ w + e(c), with translation invariance, gives 𝓛(𝔅_j)·∞ = 0, hence 𝓛(𝔅_j) = 0.

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
