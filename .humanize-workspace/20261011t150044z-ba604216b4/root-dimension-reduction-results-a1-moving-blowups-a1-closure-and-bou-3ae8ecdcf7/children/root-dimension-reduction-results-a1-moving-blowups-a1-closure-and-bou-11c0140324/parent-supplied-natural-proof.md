# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1.point_sum_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 5 (cancellation: m(y) := Σ_{i: y_i = y} ε_i and F := {y ∈ Y ∩ B_r(x₀) : m(y) ≠ 0}) and step 6 (explicit IMRep with finite carrier), here stated for an arbitrary domain V and arbitrary integer coefficients. Simon's printed proof of Ch. 6, Theorem 8.2 (book/chapter-06.txt line 2323) only says that "the theorem is trivial in case n = 0", so this argument is extracted and specialized from the parent-supplied proof of dmcbr_closure_degree_zero (Part III, CL(0)).

Notation. e : Fin 0 → ℝ^P is the empty family (Lean: fun i => i.elim0); for a 0-covector α put ⟨α⟩ := α(e). Let ev ∈ MultiVector P 0 be the continuous linear functional α ↦ α(e) (Mathlib ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ e), so ev(α) = ⟨α⟩. H⁰ = μHE[0].
1. Cancellation. For p ∈ ℝ^P let m(p) := Σ_{l<M} (if y_l = p then v_l else 0) ∈ ℤ. Let Y := {y_l : l < M} (the finset image of range M under y) and G := {p ∈ Y : p ∈ V and m(p) ≠ 0} (Finset.filter), a finite subset of V.
2. Reduced formula for S. For every φ : ℝ^P → ℝ, Σ_{l<M} v_l φ(y_l) = Σ_{p∈Y} m(p) φ(p): expand m(p) (Int.cast_sum, Int.cast_ite, Finset.sum_mul), exchange the two sums (Finset.sum_comm), and for fixed l keep only the term p = y_l ∈ Y (Finset.sum_eq_single). Let ω ∈ 𝒟^0(V) and φ(p) := ⟨ω(p)⟩. If p ∈ Y and m(p)⟨ω(p)⟩ ≠ 0, then m(p) ≠ 0 and ω(p) ≠ 0, and the latter gives p ∈ tsupport ω ⊆ V (image_eq_zero_of_notMem_tsupport). So the nonzero terms are indexed by G (Finset.sum_filter_of_ne), and S(ω) = Σ_{p∈G} m(p)⟨ω(p)⟩.
3. The triple. Define carrier := G; mult := the indicator of G applied to p ↦ |m(p)| ∈ ℕ (Int.natAbs); s := the indicator of G applied to p ↦ sign(m(p)) ∈ ℝ (Int.sign, cast to ℝ); orient(p) := s(p)·ev. For p ∈ G we have sign(m(p)) = 1 if m(p) > 0 and sign(m(p)) = −1 if m(p) < 0 (Int.sign_eq_one_of_pos, Int.sign_eq_neg_one_of_neg).
4. IMRep axioms. (a) G is finite, hence measurable (Set.Finite.measurableSet), and G ⊆ V by construction. (b) Rectifiability. If G = ∅, it is H⁰-null, hence countably 0-rectifiable (SimonGMT countablyRectifiable_of_measure_zero). Otherwise G is countable and nonempty, so G = range φ for some φ : ℕ → ℝ^P (Set.Countable.exists_eq_range). Take M₀ = ∅ and let F_j : ℝ^0 → ℝ^P be the constant map with value φ(j), which is Lipschitz with constant 0 (LipschitzWith.const). Since 0 ∈ ℝ^0, φ(j) ∈ range F_j, so G ⊆ M₀ ∪ ⋃_j range F_j, i.e. CountablyRectifiable 0 G. (c) Measurability. Each p ↦ (if y_l = p then v_l else 0) is measurable because {p : y_l = p} = {y_l} is measurable (Measurable.ite), so m is measurable as a finite sum (Finset.measurable_sum; ℤ carries the discrete σ-algebra). Every map out of ℤ is measurable (Measurable.of_discrete), so p ↦ |m(p)| and p ↦ sign(m(p)) are measurable, and so are their indicators on the measurable set G (Measurable.indicator). Thus mult and s are measurable, and orient = s(·)·ev is strongly measurable (Measurable.stronglyMeasurable, StronglyMeasurable.smul_const), in particular a.e. strongly measurable for H⁰⌞G. (d) For p ∈ G, mult(p) = |m(p)| ≥ 1 because m(p) ≠ 0 (Int.natAbs_pos). (e) For compact K ⊆ V: ∫⁻_{G∩K} mult dH⁰ ≤ ∫⁻_G mult dH⁰ (lintegral_mono_set) = Σ_{p∈G} mult(p) < ∞, by the lower-integral identity of the sibling theorem cbrz_finset_integral_hausdorff_zero (count_integral). (f) Orientation. We prove the property at every p ∈ G, which gives the H⁰⌞G-a.e. statement because G is measurable (ae_restrict_of_forall_mem). Take Q := ⊥. HasApproximateTangentSpaceAt 0 G p ⊥ is the sibling theorem dmcbrz_approxTangent_finite_zero (finite_tangent; G is finite and p ∈ G). IsUnitOrientationOf (orient p) ⊥ holds with τ := e: τ is orthonormal vacuously (Fin 0 is empty); span(range e) = span ∅ = ⊥; and orient(p)(α) = sign(m(p))⟨α⟩, which equals α(τ) for all α if m(p) > 0 and −α(τ) for all α if m(p) < 0.
5. Representation. Let ω ∈ 𝒟^0(V). By the integral identity of the sibling theorem cbrz_finset_integral_hausdorff_zero, R.action(ω) = ∫_G mult(p)·orient(p)(ω(p)) dH⁰ = Σ_{p∈G} mult(p)·s(p)⟨ω(p)⟩. On G the indicators equal their defining functions, so this is Σ_{p∈G} |m(p)|·sign(m(p))⟨ω(p)⟩ = Σ_{p∈G} m(p)⟨ω(p)⟩ (Int.sign_mul_natAbs). By step 2 this is S(ω). So R represents S, and S is integer multiplicity. ∎

Appendix (not part of the mathematical argument). The following Lean tactic proof of exactly this frozen type compiled in this decomposition session as the body of `theorem Submission.dmcbrz_isIntegerMultiplicity_point_sum : <frozen type> := by`, placed in `namespace GMT.Ch07` after `import GMT.Ch07.Submission` with the replayed contract scope (open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)), Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b366308, the sibling dependencies entering only as `have hCI := Submission.cbrz_finset_integral_hausdorff_zero` and `have hFT := Submission.dmcbrz_approxTangent_finite_zero`; `#print axioms` reports only propext, Classical.choice, Quot.sound. Compiling all five children together in one file emitted only deprecation/linter warnings (if_pos, dif_pos, push_neg, Set.Finite.diff, ContinuousLinearMap.smul_apply, unnecessary simpa).
```lean
  have hCI := Submission.cbrz_finset_integral_hausdorff_zero
  have hFT := Submission.dmcbrz_approxTangent_finite_zero
  intro P V S M v y hS
  classical
  let m : Euclid P → ℤ := fun p => ∑ l ∈ Finset.range M, if y l = p then v l else 0
  let Y : Finset (Euclid P) := (Finset.range M).image y
  let Gf : Finset (Euclid P) := Y.filter (fun p => p ∈ V ∧ m p ≠ 0)
  let ev : MultiVector P 0 := ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun i => i.elim0)
  have hev : ∀ α : Covector (Euclid P) 0, ev α = α (fun i => i.elim0) := fun α => rfl
  have hGmem : ∀ p, p ∈ Gf ↔ p ∈ Y ∧ (p ∈ V ∧ m p ≠ 0) := fun p => Finset.mem_filter
  have hGfin : (Gf : Set (Euclid P)).Finite := Gf.finite_toSet
  have hGmeas : MeasurableSet (Gf : Set (Euclid P)) := hGfin.measurableSet
  have hgroup : ∀ f : Euclid P → ℝ,
      ∑ l ∈ Finset.range M, (v l : ℝ) * f (y l) = ∑ p ∈ Y, (m p : ℝ) * f p := by
    intro f
    simp only [m, Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_eq_single (y l)]
    · simp
    · intro p _ hp
      simp [Ne.symm hp]
    · intro h
      exact absurd (Finset.mem_image_of_mem y hl) h
  have hred : ∀ ω : TestFormOn V 0, S ω =
      ∑ p ∈ Gf, (m p : ℝ) * (ω : DifferentialForm (Euclid P) 0) p (fun i => i.elim0) := by
    intro ω
    rw [hS ω, hgroup (fun p => (ω : DifferentialForm (Euclid P) 0) p (fun i => i.elim0))]
    symm
    apply Finset.sum_filter_of_ne
    intro p _ hp
    refine ⟨?_, fun h0 => hp (by simp [h0])⟩
    by_contra hpV
    apply hp
    have h0 : (ω : DifferentialForm (Euclid P) 0) p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hpV (ω.property.2 h))
    simp [h0]
  have hm : Measurable m := by
    apply Finset.measurable_sum
    intro l _
    refine Measurable.ite ?_ measurable_const measurable_const
    have h : {a : Euclid P | y l = a} = {y l} := by
      ext a
      simp [eq_comm]
    rw [h]
    exact measurableSet_singleton _
  let sgn : Euclid P → ℝ :=
    (Gf : Set (Euclid P)).indicator (fun q => ((Int.sign (m q) : ℤ) : ℝ))
  have hsgn : Measurable sgn :=
    ((Measurable.of_discrete (f := fun z : ℤ => ((Int.sign z : ℤ) : ℝ))).comp hm).indicator hGmeas
  let R : IMRep V 0 :=
    { carrier := Gf
      mult := (Gf : Set (Euclid P)).indicator (fun p => (m p).natAbs)
      orient := fun p => sgn p • ev
      measurableSet_carrier := hGmeas
      carrier_subset := fun p hp => ((hGmem p).mp hp).2.1
      rectifiable := by
        rcases (Gf : Set (Euclid P)).eq_empty_or_nonempty with h | h
        · rw [h]
          exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
        · obtain ⟨φ, hφ⟩ := hGfin.countable.exists_eq_range h
          refine ⟨∅, measure_empty, fun j _ => φ j, fun j => ⟨0, LipschitzWith.const (φ j)⟩, ?_⟩
          intro x hx
          rw [hφ] at hx
          obtain ⟨j, rfl⟩ := hx
          exact Or.inr (mem_iUnion.mpr ⟨j, ⟨0, rfl⟩⟩)
      measurable_mult :=
        ((Measurable.of_discrete (f := fun z : ℤ => z.natAbs)).comp hm).indicator hGmeas
      mult_pos := fun p hp => by
        rw [Set.indicator_of_mem hp]
        exact Int.natAbs_pos.mpr ((hGmem p).mp hp).2.2
      locallyIntegrable_mult := fun K _ _ => by
        refine ne_top_of_le_ne_top ?_ (lintegral_mono_set inter_subset_left)
        rw [(hCI P Gf (fun _ => 0) _).2]
        exact ENNReal.sum_ne_top.mpr fun p _ => ENNReal.natCast_ne_top _
      aestronglyMeasurable_orient :=
        (hsgn.stronglyMeasurable.smul_const ev).aestronglyMeasurable
      orients := by
        refine ae_restrict_of_forall_mem hGmeas fun p hp => ?_
        refine ⟨⊥, hFT P _ p hGfin hp, fun i => i.elim0,
          ⟨fun i => i.elim0, fun i => i.elim0⟩, by simp, ?_⟩
        have hmp := ((hGmem p).mp hp).2.2
        rcases lt_or_gt_of_ne hmp with hneg | hpos
        · right
          intro α
          simp [sgn, Set.indicator_of_mem hp, Int.sign_eq_neg_one_of_neg hneg, hev]
        · left
          intro α
          simp [sgn, Set.indicator_of_mem hp, Int.sign_eq_one_of_pos hpos, hev] }
  refine ⟨R, fun ω => ?_⟩
  rw [hred ω]
  change _ = ∫ x in (Gf : Set (Euclid P)),
    (((Gf : Set (Euclid P)).indicator (fun p => (m p).natAbs) x : ℕ) : ℝ) *
      (sgn x • ev) ((ω : DifferentialForm (Euclid P) 0) x) ∂μHE[0]
  rw [(hCI P Gf _ (fun _ => 0)).1]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpc : p ∈ (Gf : Set (Euclid P)) := Finset.mem_coe.mpr hp
  simp only [sgn, Set.indicator_of_mem hpc, ContinuousLinearMap.smul_apply, smul_eq_mul, hev]
  have h : ((Int.sign (m p) * ((m p).natAbs : ℤ) : ℤ) : ℝ) = (m p : ℝ) := by
    rw [Int.sign_mul_natAbs]
  simp only [Int.cast_mul, Int.cast_natCast] at h
  have h' : (((m p).natAbs : ℕ) : ℝ) * ((Int.sign (m p) : ℤ) : ℝ) = (m p : ℝ) := by
    rw [mul_comm]
    exact h
  rw [← h']
  ring
```

## Key steps

1. group the point evaluations by location: Σ_l v_l⟨ω(y_l)⟩ = Σ_{p∈Y} m(p)⟨ω(p)⟩ with m(p) = Σ_{y_l = p} v_l
2. drop points outside V (ω vanishes there) and points with m(p) = 0: S(ω) = Σ_{p∈G} m(p)⟨ω(p)⟩
3. define carrier G, mult = 1_G·|m|, orient = (1_G·sign m)·ev and verify measurability, rectifiability (finitely many points), positivity and local integrability (count_integral)
4. orientation at every p ∈ G: approximate tangent space ⊥ (finite_tangent) and ±ev is a unit orientation of ⊥
5. R.action(ω) = Σ_{p∈G} |m(p)| sign(m(p))⟨ω(p)⟩ = S(ω) (count_integral)

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db, mathlib_commit 25730c7c); git rev-parse HEAD (b4d606db); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean and cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); lake-manifest.json (simongmt 2b366308)`
- `rg -n 'hausdorffMeasure_zero|euclideanHausdorffMeasure_zero|count' over SNAPSHOT/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean and Geometry/Euclidean/Volume/Measure.lean (found euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton, one_le_hausdorffMeasure_zero_of_nonempty)`
- `rg -n 'μH\[0\].*count|count.*μH\[0\]|hausdorffMeasure_zero_eq|hausdorffMeasure.*count' SNAPSHOT/mathlib/Mathlib (no match: the library does not identify H⁰ with the counting measure)`
- `rg -n 'μH\[0\]|μHE\[0\]|Measure.count|hausdorffMeasure_zero' .lake/packages/simongmt/Poincare (only simonHausdorffMeasure_zero_singleton and finite_set_hausdorffMeasure_zero)`
- `rg -n/-F over SNAPSHOT/mathlib/Mathlib for names cited by the child proofs: setIntegral_finset, lintegral_finset, integrableOn_singleton, integrableOn_finite_biUnion, biUnion_of_singleton, Finite.exists_infinite_fiber, Nat.frequently_atTop_iff_infinite, extraction_of_frequently_atTop, isCompact_univ_pi, IsCompact.tendsto_subseq, tendsto_finsetProd (to_additive tendsto_finsetSum), Infinite.exists_subset_card_eq, Countable.exists_eq_range, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, prod_filter_of_ne (to_additive sum_filter_of_ne), image_eq_one_of_notMem_mulTSupport (to_additive image_eq_zero_of_notMem_tsupport), ContinuousAlternatingMap.apply, finrank_bot, Int.sign_mul_natAbs and Ioo_mem_nhdsGT (uses located)`
- `sed/grep on SimonGMT and contract definitions: GeometricCurrentOn, TestFormOn, WeaklyConvergesOn (Chapter06/Currents.lean); massOn, covectorEuclideanNorm, WeaklyConvergesOn.massOn_le_liminf (Chapter06/Mass.lean); restrictDomain, testFormOnInclusion (Chapter06/CurrentLocalEquality.lean); Covector, DifferentialForm (Chapter06/Forms.lean); CountablyRectifiable, countablyRectifiable_of_measure_zero, blowUpMap, HasApproximateTangentSpaceAt (Chapter03/Rectifiable.lean); IMRep, IsUnitOrientationOf, IsIntegerMultiplicity, boundaryMassOn, CompactlyContained (GMT/Ch07/Contract.lean)`
- `python3 scans of RUN/dag.json (1541 nodes): selected node (depth 4, attempt 1, no children); frozen im_local type; nodes with degree-0 titles or types; byte identity of the types of dmcbr_closure_degree_zero and cbr_closure_degree_zero (true); status and candidate_commit of cbrz_finset_integral_hausdorff_zero (accepted, fc243d0a), cbrz_point_sum_limit (accepted, 8dd8dd9f), cbrz_approxTangent_finite_zero, cbrz_imrep_zero_local_point_sum, cbrz_isIntegerMultiplicity_point_sum (speculative-ready); lean_name lookup of the three dmcbrz_ names (none); 571 existing cross-branch reuses of accepted children`
- `diff of the Part III proofs in nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/parent-supplied-natural-proof.md and nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-3ae8ecdcf7/parent-supplied-natural-proof.md (only sibling names and two clarifying parentheticals differ); read decomposition-v2.json and decomposition-audit-v1/v2.json of the former`
- `grep -rl dmcbrz RUN/nodes; rg -c 'cbrz_|dmcbrz' SNAPSHOT/project; rg -c dmcbrz .lake/packages/simongmt (all no match)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (an accepted node with identical type may be shared; an unaccepted node under another parent is reserved)`
- `grep -n 'trivial in case n D 0' and '^8.2 Theorem' book/chapter-06.txt (lines 2323 and 2303)`
- `python3 verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem); verifier/lean_contract.py validate_lean_statement on the five child types`
- `lake env lean (v4.35.0-rc3) on /tmp/dmcbrz-cl0-k7q2/lean/Types.lean (7 types elaborate), Full.lean and FromPayload.lean (five child proofs with axioms propext, Classical.choice, Quot.sound; parent assembly against an unproved im_local stub), Assembly.lean (hypothesis-only parent assembly: propext, Classical.choice, Quot.sound) and InstCheck.lean (casts and empty-family evaluation)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/Pigeonhole.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Cofinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Monoid.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/AppendixA/Foundations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-3ae8ecdcf7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-3ae8ecdcf7/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/decomposition-audit-v2.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dmcbrz-cl0-k7q2/lean/Types.lean`
- `/tmp/dmcbrz-cl0-k7q2/lean/Full.lean`
- `/tmp/dmcbrz-cl0-k7q2/lean/FromPayload.lean`
- `/tmp/dmcbrz-cl0-k7q2/lean/Assembly.lean`
- `/tmp/dmcbrz-cl0-k7q2/lean/InstCheck.lean`

Pins match (HEAD b4d606db = snapshot project commit, Mathlib 25730c7c, SimonGMT 2b366308), and Submission.lean is byte-identical to the frozen contract and its snapshot copy. Neither Mathlib nor SimonGMT identifies H⁰ with the counting measure or states any of the five obligations, and the snapshot project has no cbrz_ or dmcbrz_ declaration. The DAG already holds the byte-identical theorem cbr_closure_degree_zero with an independently audited five-way split. Its children cbrz_finset_integral_hausdorff_zero and cbrz_point_sum_limit are accepted with candidate commits and are reused with byte-identical types. The other three are unaccepted and reserved under another parent, so their propositions get the fresh, collision-free names dmcbrz_approxTangent_finite_zero, dmcbrz_imrep_zero_local_point_sum and dmcbrz_isIntegerMultiplicity_point_sum. Every library name cited by the child proofs exists in the pinned sources. All five types elaborate in the replayed contract scope. The five child proofs compile using only standard axioms. The hypothesis-only assembly proves the exact frozen parent type from im_local and the children, with axioms propext, Classical.choice and Quot.sound.
