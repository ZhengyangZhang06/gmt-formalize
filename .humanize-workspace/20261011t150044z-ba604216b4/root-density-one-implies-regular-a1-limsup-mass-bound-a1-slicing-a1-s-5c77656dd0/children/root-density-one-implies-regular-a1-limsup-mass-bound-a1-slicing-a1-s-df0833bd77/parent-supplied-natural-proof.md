# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.chart_c1_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 3. Simon Ch. 3, proof of Lemma 1.2 'only if' (chapter-03.txt lines 36–50). Ch. 2, Theorem 1.2 (Lipschitz extension, chapter-02.txt line 33) and Theorem 1.5 (C¹ approximation, line 165); the latter is the antecedent (CA).

Notation: B̄_r(c) = closedBall c r and B_r(c) = ball c r.

1. Ball cover (Lindelöf). Let 𝔅 be the set of pairs b = (c_b, r_b) ∈ ℝ^m × ℝ with r_b > 0 and B̄_{2r_b}(c_b) ⊆ V.
   - Let v ∈ V. Choose ε > 0 with B_ε(v) ⊆ V (V is open). Then B̄_{2ε/3}(v) ⊆ B_ε(v) ⊆ V, so (v, ε/3) ∈ 𝔅 and v ∈ B_{ε/3}(v).
   - Hence V ⊆ ⋃_{b∈𝔅} B_{r_b}(c_b).
   - Lindelöf (TopologicalSpace.isOpen_iUnion_countable, for the open balls B_{r_b}(c_b), b ∈ 𝔅) gives a countable T ⊆ 𝔅 with ⋃_{b∈T} B_{r_b}(c_b) = ⋃_{b∈𝔅} B_{r_b}(c_b) ⊇ V.

2. Lipschitz on a ball. Fix b ∈ T and write B̄ := B̄_{r_b}(c_b) and B̄' := B̄_{2r_b}(c_b).
   - B̄' is convex and compact, and B̄' ⊆ V, so ψ is C¹ on B̄' (ContDiffOn.mono).
   - A C¹ map on a convex compact set is Lipschitz there (ContDiffOn.exists_lipschitzOnWith). So ψ is Λ_b-Lipschitz on B̄' for some Λ_b ≥ 0.
   - Hence u_b := f∘ψ is (LΛ_b)-Lipschitz on B̄', and therefore on B̄ ⊆ B̄' (since r_b ≤ 2r_b).

3. Lipschitz extension. By McShane's theorem (Simon Ch. 2, Theorem 1.2; Mathlib LipschitzOnWith.extend_real) there is ũ_b : ℝ^m → ℝ, (LΛ_b)-Lipschitz on ℝ^m, with ũ_b = u_b on B̄. In particular ũ_b is continuous.

4. C¹ approximation. For each k ∈ ℕ apply (CA) to ũ_b (constant LΛ_b) with ε := (k+1)⁻¹ ∈ (0, ∞]. This gives a C¹ function G_{b,k} : ℝ^m → ℝ with L^m({ũ_b ≠ G_{b,k}}) < (k+1)⁻¹.

5. The pieces. For b ∈ T and k ∈ ℕ put
   - C_{b,k} := B̄ ∩ {y : ũ_b(y) = G_{b,k}(y)};
   - C'_{b,k} := B̄';
   - F_{b,k} := G_{b,k}.
   They have the following properties.
   - (i) The set {ũ_b = G_{b,k}} is closed, because both functions are continuous. So C_{b,k} is a closed subset of the compact set B̄, hence compact.
   - (ii) C'_{b,k} is compact and convex, and C'_{b,k} ⊆ V.
   - (iii) C_{b,k} ⊆ int B̄'. Every y ∈ B̄ satisfies |y − c_b| ≤ r_b < 2r_b, so y ∈ B_{2r_b}(c_b). That open ball lies in the interior of B̄' (ball_subset_interior_closedBall).
   - (iv) F_{b,k} is C¹.
   - (v) For y ∈ C_{b,k}: f(ψ(y)) = u_b(y) = ũ_b(y) = G_{b,k}(y), using y ∈ B̄.

6. Enumeration.
   - Add an index ∗ with C_∗ := C'_∗ := ∅ and F_∗ := 0. Properties (i)–(v) hold for ∗: ∅ is compact and convex, ∅ ⊆ int ∅ and ∅ ⊆ V, the zero function is C¹, and (v) is vacuous.
   - T × ℕ is countable, so (T × ℕ) ∪ {∗} (formally Option (T × ℕ)) is countable and nonempty. Let σ : ℕ → (T × ℕ) ∪ {∗} be surjective.
   - Put C_k := C_{σ(k)}, C'_k := C'_{σ(k)} and F_k := F_{σ(k)}. All per-k properties of the conclusion hold by step 5.

7. Null remainder.
   - Let v ∈ V ∖ ⋃_k C_k. By step 1, v ∈ B_{r_b}(c_b) ⊆ B̄_{r_b}(c_b) for some b ∈ T.
   - For every k ∈ ℕ choose s with σ(s) = (b, k). Since v ∉ C_s = C_{b,k} and v ∈ B̄_{r_b}(c_b), we get ũ_b(v) ≠ G_{b,k}(v).
   - Hence V ∖ ⋃_k C_k ⊆ ⋃_{b∈T} Z_b, where Z_b := ⋂_{k∈ℕ} {ũ_b ≠ G_{b,k}}.
   - For each b and every n ∈ ℕ, L^m(Z_b) ≤ L^m({ũ_b ≠ G_{b,n}}) < (n+1)⁻¹ ≤ n⁻¹.
   - If L^m(Z_b) ≠ 0, there is n with n⁻¹ < L^m(Z_b) (ENNReal.exists_inv_nat_lt), a contradiction. So L^m(Z_b) = 0.
   - T is countable, and a countable union of null sets is null. So L^m(V ∖ ⋃_k C_k) = 0. ∎

Appendix — Lean proof of the frozen type. Compiled against Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, in the exact comparator scope. Axioms: propext, Classical.choice, Quot.sound.
```lean
  classical
  intro CA m P V ψ f L hV hψ hf
  let B := {p : Euclid m × ℝ // 0 < p.2 ∧ closedBall p.1 (2 * p.2) ⊆ V}
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun b : B => ball b.1.1 b.1.2) (fun _ => isOpen_ball)
  have hcovV : V ⊆ ⋃ b ∈ T, ball b.1.1 b.1.2 := by
    intro v hv
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV v hv
    have hsub : closedBall v (2 * (ε / 3)) ⊆ V :=
      (closedBall_subset_ball (by linarith)).trans hball
    let b : B := ⟨(v, ε / 3), by positivity, hsub⟩
    rw [hTU]
    exact mem_iUnion.2 ⟨b, mem_ball_self (by positivity)⟩
  have hdata : ∀ b : B, ∃ (G : ℕ → Euclid m → ℝ) (u : Euclid m → ℝ), (∀ k, ContDiff ℝ 1 (G k)) ∧
      Continuous u ∧ (∀ y ∈ closedBall b.1.1 b.1.2, f (ψ y) = u y) ∧
      ∀ k : ℕ, volume {y | u y ≠ G k y} < ((k : ℝ≥0∞) + 1)⁻¹ := by
    intro b
    obtain ⟨Λ, hΛ⟩ := (hψ.mono b.2.2).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
      (isCompact_closedBall _ _)
    have hu : LipschitzOnWith (L * Λ) (f ∘ ψ) (closedBall b.1.1 b.1.2) :=
      (hf.comp_lipschitzOnWith hΛ).mono (closedBall_subset_closedBall (by linarith [b.2.1]))
    obtain ⟨u, hu', hequ⟩ := hu.extend_real
    have hk : ∀ k : ℕ, ∃ G : Euclid m → ℝ, ContDiff ℝ 1 G ∧
        volume {y | u y ≠ G y} < ((k : ℝ≥0∞) + 1)⁻¹ := fun k =>
      CA m u (L * Λ) hu' _ (ENNReal.inv_pos.2 (by simp))
    choose G hG hGvol using hk
    exact ⟨G, u, hG, hu'.continuous, fun y hy => hequ hy, hGvol⟩
  choose G u hG hucont hequ hGvol using hdata
  haveI : Countable T := hTc.to_subtype
  let Cp : Option (T × ℕ) → Set (Euclid m) := fun o =>
    match o with
    | none => ∅
    | some (b, k) => closedBall b.1.1.1 b.1.1.2 ∩ {y | u b.1 y = G b.1 k y}
  let C'p : Option (T × ℕ) → Set (Euclid m) := fun o =>
    match o with
    | none => ∅
    | some (b, _) => closedBall b.1.1.1 (2 * b.1.1.2)
  let Fp : Option (T × ℕ) → Euclid m → ℝ := fun o =>
    match o with
    | none => 0
    | some (b, k) => G b.1 k
  have hprop : ∀ o, IsCompact (Cp o) ∧ IsCompact (C'p o) ∧ Convex ℝ (C'p o) ∧
      Cp o ⊆ interior (C'p o) ∧ C'p o ⊆ V ∧ ContDiff ℝ 1 (Fp o) ∧
      ∀ y ∈ Cp o, f (ψ y) = Fp o y := by
    intro o
    cases o with
    | none => exact ⟨isCompact_empty, isCompact_empty, convex_empty, empty_subset _, empty_subset _,
        contDiff_zero_fun, fun y hy => hy.elim⟩
    | some bk =>
      obtain ⟨b, k⟩ := bk
      refine ⟨(isCompact_closedBall _ _).inter_right
          (isClosed_eq (hucont b.1) (hG b.1 k).continuous),
        isCompact_closedBall _ _, convex_closedBall _ _, ?_, b.1.2.2, hG b.1 k, ?_⟩
      · intro y hy
        apply ball_subset_interior_closedBall
        have := hy.1
        rw [mem_closedBall] at this
        rw [mem_ball]
        linarith [b.1.2.1]
      · intro y hy
        exact (hequ b.1 y hy.1).trans hy.2
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (Option (T × ℕ))
  refine ⟨fun s => Cp (σ s), fun s => C'p (σ s), fun s => Fp (σ s), fun s => hprop (σ s), ?_⟩
  have hsub : V \ ⋃ s, Cp (σ s) ⊆ ⋃ b : T, ⋂ k : ℕ, {y | u b.1 y ≠ G b.1 k y} := by
    rintro v ⟨hv, hvnot⟩
    obtain ⟨b, hbT, hvb⟩ := mem_iUnion₂.1 (hcovV hv)
    refine mem_iUnion.2 ⟨⟨b, hbT⟩, mem_iInter.2 fun k => ?_⟩
    intro heq
    obtain ⟨s, hs⟩ := hσ (some (⟨b, hbT⟩, k))
    apply hvnot
    refine mem_iUnion.2 ⟨s, ?_⟩
    rw [hs]
    exact ⟨ball_subset_closedBall hvb, heq⟩
  refine measure_mono_null hsub (measure_iUnion_null fun b => ?_)
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
  have h1 : volume (⋂ k : ℕ, {y | u b.1 y ≠ G b.1 k y}) ≤ ((n : ℝ≥0∞) + 1)⁻¹ :=
    (measure_mono (iInter_subset _ n)).trans (hGvol b.1 n).le
  have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_le_inv.2 le_self_add
  exact absurd (h1.trans h2) (not_le.2 hn)
```

## Key steps

1. Balls b = (c, r) with r > 0 and B̄_{2r}(c) ⊆ V cover V; Lindelöf gives a countable subfamily T.
2. ψ is Lipschitz on the convex compact B̄_{2r}(c) (ContDiffOn.exists_lipschitzOnWith), so f∘ψ is Lipschitz on B̄_r(c); take its McShane extension ũ_b (LipschitzOnWith.extend_real).
3. (CA) with ε = (k+1)⁻¹ gives C¹ functions G_{b,k} with L^m{ũ_b ≠ G_{b,k}} < (k+1)⁻¹.
4. C_{b,k} = B̄_r(c) ∩ {ũ_b = G_{b,k}} is compact and lies in B_{2r}(c) ⊆ int B̄_{2r}(c); C' = B̄_{2r}(c) is convex, compact and ⊆ V; f∘ψ = G_{b,k} on C_{b,k}.
5. Enumerate Option (T × ℕ) by ℕ, using the empty piece for none.
6. V ∖ ⋃ C ⊆ ⋃_{b∈T} ⋂_k {ũ_b ≠ G_{b,k}}; each intersection has measure < (n+1)⁻¹ for every n, hence 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); manifest.json (project b4d606d, mathlib 25730c7c); lakefile.toml simongmt rev 2b36630`
- `python3 -I dag.json scans: frozen lean_statement/status of slice_family-a1 children c1_approx, c1_cover, image_tangent, density_directions; selected node status/depth/lean_statement; regex scan for related nodes (disjoint_refinement|image_null|IsEmbeddedSubmanifold 1|tangential gradient|density point|adjoint); lean_name collision check for dor_lmbsf_cp_* (1535 nodes, none)`
- `git grep -l dor_lmbsf_cp_ over all local branch heads (no match); git show <recent branch>:GMT/Ch07/Submission.lean | grep import (extra imports are allowed but not needed)`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique' simongmt Chapter03/Rectifiable.lean; grep -n euclideanHausdorffMeasure_image_le_of_lipschitzOn simongmt Chapter02/Lipschitz.lean; grep -rln 'import Mathlib.Topology.MetricSpace.HausdorffDimension' simongmt`
- `grep mathlib snapshot: isOpen_iUnion_countable, ContinuousOn.isOpen_inter_preimage, LipschitzOnWith.extend_real, ContDiffOn.exists_lipschitzOnWith, ContDiffAt.exists_lipschitzOnWith, DifferentiableOn.hausdorffMeasure_image_eq_zero, euclideanHausdorffMeasure_def/_eq_volume, ae_tendsto_measure_inter_div_of_measurableSet, HasFDerivWithinAt.lim, exists_measurable_superset_of_null, MeasurableSet.image_of_continuousOn_injOn, ContinuousOn.measurableEmbedding, ContinuousOn.measurable_piecewise, Measurable.find, MeasurableEmbedding.measurable_extend, ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot, NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint_inner_left, disjointed/iUnion_disjointed/MeasurableSet.disjointed`
- `#check and instance probes in the contract scope (/tmp/cp-decomp/probe/Probe.lean, Probe2.lean): isOpen_iUnion_countable must be TopologicalSpace-qualified; DifferentiableOn.hausdorffMeasure_image_eq_zero is not in the import closure; IsLocallyFiniteMeasure volume, HasBesicovitchCovering, PolishSpace, BorelSpace and CompleteSpace instances on Euclid m resolve`
- `python3 -I verifier lean_contract.validate_lean_statement and gmt-compare.child_modules on the 8 statements; lake env lean on /tmp/cp-decomp/v2/Final.lean (8 child proofs plus the parent assembly; #print axioms)`
- `book/chapter-03.txt lines 20–140 and 320–445 (Lemma 1.2, Remark 1.3, Remarks 1.5, proof of Thm 1.6, Def. 2.1); book/chapter-02.txt lines 33, 59–62, 165 (Thms 1.2, 1.4, 1.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-5c77656dd0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/cp-decomp/v2/Final.lean`

Snapshot: project b4d606d, mathlib 25730c7c, simongmt 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reuse. No existing declaration has any of the 8 child types. Related accepted nodes have different types:
- cbrg_exists_countable_disjoint_refinement;
- dsmc_att_blowUpMap_image_null;
- cmr_volume_coordProj_image_null;
- approxTangent_le_submanifold_tangentSpace.
So all children get fresh dor_lmbsf_cp_ names.

Reusable library facts used by the child proofs:
- SimonGMT: Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- Mathlib topology and analysis: TopologicalSpace.isOpen_iUnion_countable (Lindelöf), LipschitzOnWith.extend_real (McShane), ContDiffOn.exists_lipschitzOnWith, ContDiffAt.exists_lipschitzOnWith, HasFDerivWithinAt.lim.
- Mathlib measure theory: Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, exists_measurable_superset_of_null, ContinuousOn.measurable_piecewise, MeasurableSet.image_of_continuousOn_injOn / ContinuousOn.measurableEmbedding (Lusin–Souslin), MeasurableEmbedding.measurable_extend, Measurable.find.
- Mathlib operators: ContinuousLinearMap.adjoint, NormedRing.inverse_continuousAt, ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.
- DifferentiableOn.hausdorffMeasure_image_eq_zero exists but needs an extra import, so c1_image_null uses the self-contained local-Lipschitz route.

Lean checks:
- All 8 child types elaborate in the exact comparator scope.
- All 8 are proved, each with axioms [propext, Classical.choice, Quot.sound].
- The exact frozen parent type is assembled from them plus the 4 uncle frozen types; its only sorryAx comes from the uncle stubs.
