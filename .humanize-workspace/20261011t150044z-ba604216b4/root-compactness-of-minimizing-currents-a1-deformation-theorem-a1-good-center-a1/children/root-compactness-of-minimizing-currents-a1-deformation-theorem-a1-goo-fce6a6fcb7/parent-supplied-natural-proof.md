# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.good_center-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.good_center-a1.cube_selection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 6, proof of 5.1: display (5) and the choice of a point a ∈ ⋂_{j=1}^{N} p_j^{-1}(G_j) ∩ B_{1/4}(q) (book/chapter-06.txt lines 1695–1705). Also the remark after (6) that β can be taken so large that one a is good for T and for ∂T simultaneously (lines 1715–1721). This is step 3 of the parent proof: Fubini over S_J × S_J^⊥ and the union bound over J.

Departures from the printed text, none of which changes the argument:
(i) The centre region is the open cube Q = (1/4, 3/4)^P instead of the ball B_{1/4}(q). Its points satisfy exactly |a_i − 1/2| < 1/4, which is what the parent needs.
(ii) The projection p_J is written x ↦ (x_{e(k)})_k for an injective e : Fin d → Fin P enumerating J, with one set E_e per map e; non-injective maps are ignored.
(iii) The fibre of the centre region over a point of S_J lies in the complementary cube, of volume (1/2)^{P−d} ≤ 1. In the printed proof it lies in a ball of radius 1/4 in the (ℓ−1)-dimensional space S_J^⊥, of volume at most ω_{ℓ−1}4^{1−ℓ}. Erratum: printed (5) has the factor ω_{n+1}/ω_{n+ℓ} where this Fubini computation gives ω_{n+1}ω_{ℓ−1}/ω_{n+ℓ}. The parent proof's step 3 corrects this constant, and the issue does not arise with cubes.
(iv) Simon shows that the good sets for T and for ∂T each fill more than half of B_{1/4}(q), and picks one a in both (lines 1715–1721). Here the bad sets of both measures are combined into one set E_e. It plays the role of B_J(μ) ∪ B_J(μ') of the parent proof, in the coordinates of S_J; the parent's Bad_J corresponds to A_e in step 3. So a single union bound suffices.
(v) The sets E_e need not be measurable, since every estimate is an outer-measure estimate.

Notation. volume on Euclid P is Lebesgue measure; volume on a function space ι → ℝ (ι finite) is the product Lebesgue measure. I := (1/4, 3/4). Note |t − 1/2| < 1/4 ⟺ t ∈ I.

1. (The cube.) Let Q := {a ∈ Euclid P : a_i ∈ I for all i}. The coordinate map ofLp : Euclid P → (Fin P → ℝ) is a volume-preserving measurable equivalence (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp). For such an equivalence, volume(ofLp^{-1}(X)) = volume(X) for every set X (MeasurePreserving.measure_preimage_equiv). Since Q = ofLp^{-1}(∏_{i<P} I), volume(Q) = ∏_{i<P} (3/4 − 1/4) = (1/2)^P (Real.volume_pi_Ioo).
2. (Fubini bound.) Let e : Fin d → Fin P be injective and F ⊆ (Fin d → ℝ) any set, and put W := {x ∈ Fin P → ℝ : x_i ∈ I for all i, and (x_{e(k)})_k ∈ F}. Then volume(W) ≤ volume(F).
 Proof. Let p(i) :⟺ i ∈ range(e). The map Φ(x) := ((x_i)_{p(i)}, (x_i)_{¬p(i)}) is a measurable equivalence (Fin P → ℝ) ≃ ({i // p i} → ℝ) × ({i // ¬p i} → ℝ) carrying volume to the product of the volumes (volume_preserving_piEquivPiSubtypeProd). Let σ : Fin d ≃ {i // p i}, σ(k) := e(k) (Equiv.ofInjective, which uses injectivity). For u : {i // p i} → ℝ put ψ(u) := (u_{σ(k)})_k. Then ψ is the inverse of the measurable equivalence MeasurableEquiv.piCongrLeft for σ, which is volume preserving (volume_measurePreserving_piCongrLeft), so volume(ψ^{-1}(F)) = volume(F). Put G := ψ^{-1}(F) and H := ∏_{i : ¬p(i)} I. If x ∈ W then Φ(x) ∈ G × H, because ψ((x_i)_{p(i)}) = (x_{e(k)})_k ∈ F and x_i ∈ I for every i. Hence
 volume(W) ≤ volume(Φ^{-1}(G × H)) = volume(G × H) = volume(G) · volume(H) = volume(F) · (1/2)^{#{i : ¬p(i)}} ≤ volume(F).
 The second step uses that Φ preserves measure. The third uses Measure.prod_prod, which holds for arbitrary sets. The fourth uses volume(H) = ∏ (1/2) ≤ 1 (Real.volume_pi_Ioo).
3. (Bad centres.) For each map e : Fin d → Fin P let A_e := {a ∈ Q : (a_{e(k)})_k ∈ E_e} if e is injective, and A_e := ∅ otherwise. For injective e, A_e = ofLp^{-1}(W) with W as in 2 for F := E_e, so steps 1 and 2 give volume(A_e) = volume(W) ≤ volume(E_e). For non-injective e, volume(A_e) = 0 ≤ volume(E_e).
4. (Union bound.) Suppose, for contradiction, that every a ∈ Q has some injective e with (a_{e(k)})_k ∈ E_e; then Q ⊆ ⋃_e A_e. Monotonicity, finite subadditivity over the finitely many maps e (measure_iUnion_fintype_le), step 3 and the hypothesis give
 (1/2)^P = volume(Q) ≤ Σ_e volume(A_e) ≤ Σ_e volume(E_e) < (1/2)^P,
 a contradiction.
5. Therefore some a ∈ Q satisfies (a_{e(k)})_k ∉ E_e for every injective e : Fin d → Fin P. Also a ∈ Q means |a_i − 1/2| < 1/4 for every i. This is the claim. ∎

Appendix (supplementary, machine-checked; not needed for the argument above). The following Lean 4 declaration, placed in GMT/Ch07/Submission.lean inside `namespace GMT.Ch07` after the contract's closing `end` of the noncomputable section (so with the contract's `open`s), follows the numbered steps above. It was compiled with `lake env lean` against the pinned workspace (Lean v4.35.0-rc3, Mathlib 25730c7c); `#print axioms` reports only propext, Classical.choice, Quot.sound.

theorem Submission.cmcdt_gc_cube_selection : ∀ (P d : ℕ) (E : (Fin d → Fin P) → Set (Fin d → ℝ)), ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ e : Fin d → Fin P, Function.Injective e → (fun k => a (e k)) ∉ E e := by
  classical
  intro P d E hsum
  -- Step 2 (Fubini): for injective `e`, the centres in the cube whose `e`-projection lies in `F`
  -- have volume at most `volume F`
  have fubini : ∀ e : Fin d → Fin P, Function.Injective e → ∀ F : Set (Fin d → ℝ),
      volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ≤
        volume F := by
    intro e he F
    let p : Fin P → Prop := fun i => i ∈ range e
    let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    have hΦ : MeasurePreserving Φ := by
      convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    let σ : Fin d ≃ {i // p i} := Equiv.ofInjective e he
    let ψ := (MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm
    have hψ : MeasurePreserving ψ :=
      (volume_measurePreserving_piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm _
    have hψapp : ∀ u k, ψ u k = u (σ k) := by
      intro u k
      simp [ψ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
    let G : Set ({i // p i} → ℝ) := ψ ⁻¹' F
    let H : Set ({i // ¬ p i} → ℝ) := Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)
    have hsub : {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ⊆
        Φ ⁻¹' (G ×ˢ H) := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, fun i _ => hx1 i⟩
      show ψ (fun i => x i) ∈ F
      have : ψ (fun i : {i // p i} => x i) = fun k => x (e k) := by
        funext k; rw [hψapp]; rfl
      rw [this]; exact hx2
    have hG : volume G = volume F := hψ.measure_preimage_equiv F
    have hH : volume H ≤ 1 := by
      rw [Real.volume_pi_Ioo]
      refine Finset.prod_le_one fun i _ => ?_
      rw [ENNReal.ofReal_le_one]; norm_num
    calc volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F}
        ≤ volume (Φ ⁻¹' (G ×ˢ H)) := measure_mono hsub
      _ = volume (G ×ˢ H) := hΦ.measure_preimage_equiv _
      _ = volume G * volume H := by
          rw [Measure.volume_eq_prod]; exact Measure.prod_prod G H
      _ ≤ volume G * 1 := by gcongr
      _ = volume F := by rw [mul_one, hG]
  have hI : ∀ t : ℝ, |t - 1 / 2| < 1 / 4 ↔ t ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
    intro t
    rw [abs_sub_lt_iff, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  -- Step 1: the open cube `Q` in `Euclid P` has volume `(1/2)^P`
  let Q : Set (Euclid P) := {a | ∀ i, a i ∈ Ioo (1 / 4 : ℝ) (3 / 4)}
  have hofLp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin P)
  have hQ : volume Q = ENNReal.ofReal ((1 / 2) ^ P) := by
    have : Q = (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
        (Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)) := by
      ext a; simp [Q, Set.mem_pi]
    rw [this, hofLp.measure_preimage_equiv, Real.volume_pi_Ioo, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num)]
    norm_num
  -- Step 3: the sets of centres with a bad projection
  let A : (Fin d → Fin P) → Set (Euclid P) := fun e =>
    {a | Function.Injective e ∧ a ∈ Q ∧ (fun k => a (e k)) ∈ E e}
  have hA : ∀ e, volume (A e) ≤ volume (E e) := by
    intro e
    by_cases he : Function.Injective e
    · have hsub : A e ⊆ (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
          {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ E e} := by
        rintro a ⟨-, haQ, haE⟩
        exact ⟨haQ, haE⟩
      calc volume (A e) ≤ _ := measure_mono hsub
        _ = _ := hofLp.measure_preimage_equiv _
        _ ≤ volume (E e) := fubini e he (E e)
    · have : A e = ∅ := by
        ext a; simp only [mem_empty_iff_false, iff_false]; exact fun h => he h.1
      rw [this, measure_empty]; exact bot_le
  -- Steps 4–5: union bound and choice of `a`
  by_contra hcon
  push Not at hcon
  have hcov : Q ⊆ ⋃ e, A e := by
    intro a haQ
    obtain ⟨e, he, haE⟩ := hcon a fun i => (hI _).2 (haQ i)
    exact mem_iUnion.2 ⟨e, he, haQ, haE⟩
  have : volume Q < volume Q :=
    calc volume Q ≤ volume (⋃ e, A e) := measure_mono hcov
      _ ≤ ∑ e, volume (A e) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ e, volume (E e) := Finset.sum_le_sum fun e _ => hA e
      _ < ENNReal.ofReal ((1 / 2) ^ P) := hsum
      _ = volume Q := hQ.symm
  exact lt_irrefl _ this

## Key steps

1. The open cube Q = (1/4, 3/4)^P in Euclid P has volume (1/2)^P: ofLp is a volume-preserving measurable equivalence, and Real.volume_pi_Ioo applies.
2. For injective e, split the coordinates into range(e) and its complement (volume_preserving_piEquivPiSubtypeProd, volume_measurePreserving_piCongrLeft, Measure.prod_prod). This gives volume{x ∈ cube : (x_{e(k)})_k ∈ F} ≤ volume(F)·(1/2)^{P−d} ≤ volume(F) for every set F (cube analogue of the corrected printed (5)).
3. So the centres in Q with a bad e-projection have volume ≤ volume(E_e). Summing over the finitely many e gives a total < (1/2)^P = volume(Q), so some a ∈ Q avoids all of them.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD = git -C .lake/packages/mathlib rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d (matches manifest.json)`
- `rg -n -i 'vitali|good.?cent|dual skeleton|cmcdt_gc|bad set' project -g '*.lean' (only Ch01 HasSymmetricVitaliProperty contract text)`
- `rg -n 'DeformationTheorem|IsLatticeChain' project/GMT/Ch06/Contract.lean (separate Ch06 contract over Eucl, main_theorem := by sorry)`
- `grep -rn 'theorem (exists_disjoint_subfamily_covering_enlargement|volume_pi_ball|volume_pi_Ioo|prod_prod|volume_preserving_piEquivPiSubtypeProd|volume_measurePreserving_piCongrLeft|infDist_lt_iff|le_map_apply|measure_preimage_equiv|EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp|EuclideanSpace.dist_eq|measure_biUnion|measure_biUnion_le|measure_iUnion_fintype_le)|lemma (dist_pi_lt_iff|exists_subset_card_eq)|Set.PairwiseDisjoint.countable_of_isOpen' mathlib/Mathlib (all found)`
- `rg -n -i 'vitali|covering_enlargement|deformation' lake-packages-25730c7c/simongmt/Poincare -g '*.lean' (only Chapter02/WhitneyCover.lean Vitali use and Chapter08 deformation families)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json: lean_name duplicates (none), cmcdt_* names of the siblings, and the three proposed names (unreserved)`
- `git log --all --oneline -S cmcdt_gc_ -- GMT/Ch07/Submission.lean over 4163 refs (no match); grep -rl cmcdt_gc_ workspaces/.swarm-worktrees/*/gmt-ch07/GMT (no match)`
- `python3 contract_scope() from verifier/gmt-compare.py on GMT/Ch07/Contract.lean (open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end)`
- `lake env lean /tmp/gc-a2-verify/lean/{InstCheck,Types,Assembly,Final2,Final2OpenReal}.lean (all EXIT=0; Final2: propext, Classical.choice, Quot.sound)`
- `sed -n 1476,1530p and 1651,1721p book/chapter-06.txt (notation before 5.4, display (2) of the proof of 5.4, proof of 5.1 displays (1)-(7))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/gc-a2-verify/lean/Types.lean`
- `/tmp/gc-a2-verify/lean/Assembly.lean`
- `/tmp/gc-a2-verify/lean/Final2.lean`
- `/tmp/gc-a2-verify/lean/InstCheck.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace Contract.lean and Submission.lean. The project has no Ch07-usable lemma for good centres, periodic tubes, Vitali packing or Fubini selection. Ch01's symmetric-Vitali material and Ch06's DeformationTheorem/IsLatticeChain belong to separate problems, use incompatible types, and have sorry proofs. simongmt has nothing reusable either. The pinned Mathlib provides every tool the children cite: Vitali.exists_disjoint_subfamily_covering_enlargement (Covering/Vitali.lean:59; its docstring confirms that the whole-ball enlargement is (1+2τ)r = 5r for τ = 2), Real.volume_pi_ball and Real.volume_pi_Ioo, Set.PairwiseDisjoint.countable_of_isOpen, measure_biUnion, measure_biUnion_le, measure_iUnion_fintype_le, Measure.le_map_apply, volume_preserving_piEquivPiSubtypeProd, volume_measurePreserving_piCongrLeft, Measure.prod_prod (arbitrary sets), MeasurePreserving.measure_preimage_equiv, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, Metric.infDist_lt_iff, Finset.exists_subset_card_eq, EuclideanSpace.dist_eq and dist_pi_lt_iff. The three child names are unreserved. All child types elaborate in the comparator's replayed contract scope. Scratch proofs of all three children, and the assembly of the byte-identical frozen parent type from them, compile with only propext, Classical.choice and Quot.sound.
