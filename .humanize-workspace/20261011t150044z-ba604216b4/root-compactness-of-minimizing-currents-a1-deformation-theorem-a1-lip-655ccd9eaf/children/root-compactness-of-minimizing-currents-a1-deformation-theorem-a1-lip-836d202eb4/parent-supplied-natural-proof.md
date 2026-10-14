# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1.orientation_sign-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 (sign, B2′) of the supplied proof, for one piece and with ζ := ξ∘G_i; the sign s_i of the supplied proof is exactly the function s constructed here.

Notation: λ := volume on ℝⁿ; e_a := EuclideanSpace.single a 1; DG(u) := fderiv ℝ G u (the zero map where G is not differentiable); v(u) := (DG(u)e_a)_{a ∈ Fin n} ∈ (ℝ^N)^n; J(u) := √det(⟨v_a(u), v_b(u)⟩)_{a,b}. For z ∈ (ℝ^N)^n let ev_z ∈ Λ_n(ℝ^N) = (Covector (Euclid N) n →L[ℝ] ℝ) be the evaluation functional α ↦ α(z) (Mathlib ContinuousAlternatingMap.apply ℝ (Euclid N) ℝ z).

1. (z ↦ ev_z is continuous.) For z, z' ∈ (ℝ^N)^n and every n-covector α, |α(z) − α(z')| ≤ ‖α‖·n·max(‖z‖, ‖z'‖)^{n−1}·‖z − z'‖ (ContinuousAlternatingMap.norm_image_sub_le). By the definition of the operator norm (ContinuousLinearMap.opNorm_le_bound), ‖ev_z − ev_{z'}‖ ≤ n·max(‖z‖, ‖z'‖)^{n−1}·‖z − z'‖. For fixed z', the right side tends to 0 as z → z'. So z ↦ ev_z is continuous.
2. (v and J are Borel.) For each a, u ↦ DG(u)e_a is Borel (measurable_fderiv_apply_const; no assumption on G is needed). Hence u ↦ v(u) ∈ (ℝ^N)^n is Borel (measurability of a map into a finite product). The map z ↦ √det(⟨z_a, z_b⟩)_{a,b} is continuous on (ℝ^N)^n (inner products, the determinant as a polynomial in the entries, the square root). So J is Borel.
3. (The comparison function.) g(u) := J(u)^{-1}·ev_{v(u)} defines a strongly measurable map ℝⁿ → Λ_n(ℝ^N). Indeed, u ↦ J(u)^{-1} is Borel and real-valued, hence strongly measurable. (ℝ^N)^n is second countable, so v is strongly measurable. Then u ↦ ev_{v(u)} is strongly measurable by step 1 (a continuous map after a strongly measurable one). Finally the scalar product of two strongly measurable maps is strongly measurable.
4. (The sign.) Let ζ' be a strongly measurable map with ζ = ζ' λ⌞A-a.e. (AEStronglyMeasurable.mk, ae_eq_mk). Λ_n(ℝ^N) is a normed space, hence metrizable, so S := {u : ζ'(u) = g(u)} is Borel (StronglyMeasurable.measurableSet_eq_fun). Define s(u) := 1 for u ∈ S and s(u) := −1 for u ∉ S. Then s is measurable (Measurable.ite with constant branches), and s(u) ∈ {1, −1} for every u.
5. (A full-measure set.) For λ⌞A-a.e. u, the following three facts hold together: ζ(u) = ζ'(u) (step 4); ζ(u) is a unit orientation of V_u := span{v_a(u) : a} (hypothesis); and u ∈ A (ae_restrict_mem, A Borel). Fix such u and an n-covector α.
6. (Linear independence.) DG(u) is injective since u ∈ A, and (e_a)_a is a basis of ℝⁿ (EuclideanSpace.basisFun). So v(u) = DG(u)∘e is linearly independent (LinearIndependent.map' with ker DG(u) = ⊥).
7. (The oriented Jacobian.) Apply cmcdt_lpi_unit_orientation_span to v(u). (It is a resolved dependency of the parent node; this child receives it as an inherited prerequisite.) It gives: (a) det(⟨v_a(u), v_b(u)⟩) > 0, so J(u) > 0; (b) some ξ_u ∈ Λ_n(ℝ^N) that is a unit orientation of V_u with α'(v(u)) = J(u)·ξ_u(α') for every n-covector α'; (c) every unit orientation of V_u equals ξ_u or −ξ_u. By (a) and (b), ξ_u(α') = J(u)^{-1}·α'(v(u)) = (J(u)^{-1}·ev_{v(u)})(α') for every α', so ξ_u = g(u).
8. (Case u ∈ S.) Then s(u) = 1 and ζ(u) = ζ'(u) = g(u). Hence J(u)·ζ(u)(α) = J(u)·J(u)^{-1}·α(v(u)) = α(v(u)) = s(u)·α(v(u)), using J(u) ≠ 0.
9. (Case u ∉ S.) Then s(u) = −1 and ζ(u) = ζ'(u) ≠ g(u) = ξ_u. By step 5 and 7(c), ζ(u) ∈ {ξ_u, −ξ_u}, so ζ(u) = −ξ_u. Hence J(u)·ζ(u)(α) = −J(u)·ξ_u(α) = −α(v(u)) = s(u)·α(v(u)), by 7(b).
10. Steps 8 and 9 give J(u)·ζ(u)(α) = s(u)·α(v(u)) for every α and every u in the full-measure set of step 5. Together with step 4, this proves the statement. No nondegeneracy ξ_u ≠ 0 is needed: the case split is on whether ζ'(u) equals g(u). ∎

Lean note (instances under the contract imports). Λ_n(ℝ^N) = MultiVector N n carries the topology ContinuousLinearMap.topologicalSpace. It is definitionally equal to the operator-norm topology, but not reducibly so. Hence instance search does not find TopologicalSpace.MetrizableSpace (MultiVector N n). Provide it inside a `have` with `let : MetricSpace (MultiVector N n) := inferInstance; exact inferInstance`. For step 1, prove continuity for the explicit norm topology `@Continuous _ _ _ PseudoMetricSpace.toUniformSpace.toTopologicalSpace ev`; a plain `exact` then converts it. For the distance write `dist_eq_norm (E := MultiVector N n)`. The reference proof below does exactly this.

Lean reference proof (verified). The declaration below was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) in a scratch file that imports GMT.Ch07.Submission and uses the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `namespace GMT.Ch07`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`). The prerequisites it applies (Submission.cmcdt_lpi_unit_orientation_span) were declared before it with their exact frozen types and `sorry` bodies; `#print axioms` reports propext, Classical.choice and Quot.sound, plus sorryAx coming only from those stubs. It follows the numbered proof above step by step.

```lean
theorem Submission.cmcdt_lpi_pr_orientation_sign : ∀ (N n : ℕ) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (ζ : Euclid n → MultiVector N n), MeasurableSet A → (∀ u ∈ A, Injective (fderiv ℝ G u)) → AEStronglyMeasurable ζ (volume.restrict A) → (∀ᵐ u ∂(volume.restrict A), IsUnitOrientationOf (ζ u) (Submodule.span ℝ (Set.range (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))))) → ∃ s : Euclid n → ℤ, Measurable s ∧ (∀ u, s u = 1 ∨ s u = -1) ∧ ∀ᵐ u ∂(volume.restrict A), ∀ α : Covector (Euclid N) n, Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1)) (fderiv ℝ G u (EuclideanSpace.single b 1)))) * ζ u α = (s u : ℝ) * α (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) := by
  intro N n G A ζ hA hinj hζ hor
  classical
  -- the evaluation functional `ev_z(α) = α(z)` depends continuously on `z`
  let ev : (Fin n → Euclid N) → MultiVector N n := fun z =>
    ContinuousAlternatingMap.apply ℝ (Euclid N) ℝ z
  have hevb : ∀ z z₀ : Fin n → Euclid N,
      ‖ev z - ev z₀‖ ≤ n * (max ‖z‖ ‖z₀‖) ^ (n - 1) * ‖z - z₀‖ := by
    intro z z₀
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro α
    have h := α.norm_image_sub_le z z₀
    simp only [Fintype.card_fin] at h
    calc ‖(ev z - ev z₀) α‖ = ‖α z - α z₀‖ := rfl
      _ ≤ ‖α‖ * n * max ‖z‖ ‖z₀‖ ^ (n - 1) * ‖z - z₀‖ := h
      _ = _ := by ring
  have hev : Continuous ev := by
    have hc : @Continuous _ _ _ (PseudoMetricSpace.toUniformSpace.toTopologicalSpace) ev := by
      rw [Metric.continuous_iff]
      intro z₀ ε hε
      have hcb : Continuous fun z : Fin n → Euclid N =>
          (n : ℝ) * (max ‖z‖ ‖z₀‖) ^ (n - 1) * ‖z - z₀‖ := by fun_prop
      obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.mp hcb z₀ ε hε
      refine ⟨δ, hδ, fun z hz => ?_⟩
      have h1 := hδε z hz
      simp only [sub_self, norm_zero, mul_zero, Real.dist_eq, sub_zero] at h1
      have h2 : dist (ev z) (ev z₀) = ‖ev z - ev z₀‖ := dist_eq_norm (E := MultiVector N n) _ _
      rw [h2]
      exact lt_of_le_of_lt (hevb z z₀) (lt_of_le_of_lt (le_abs_self _) h1)
    exact hc
  have : TopologicalSpace.MetrizableSpace (MultiVector N n) := by
    let : MetricSpace (MultiVector N n) := inferInstance
    exact inferInstance
  -- measurability of `v(u) = (DG(u)e_a)_a` and of the Jacobian `J`
  have hvm : Measurable fun u => (fun a => fderiv ℝ G u (EuclideanSpace.single a 1) :
      Fin n → Euclid N) := by
    exact Measurable.of_eval fun a => measurable_fderiv_apply_const ℝ G _
  have hJm : Measurable fun u => Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n =>
      inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1))
        (fderiv ℝ G u (EuclideanSpace.single b 1)))) := by
    have hc : Continuous fun z : Fin n → Euclid N =>
        Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (z a) (z b))) := by
      refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
      refine continuous_matrix fun a b => ?_
      fun_prop
    exact hc.measurable.comp hvm
  have hgm : StronglyMeasurable fun u =>
      (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n =>
        inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1))
          (fderiv ℝ G u (EuclideanSpace.single b 1)))))⁻¹ •
        ev (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) :=
    hJm.inv.stronglyMeasurable.smul (hev.comp_stronglyMeasurable hvm.stronglyMeasurable)
  have hset := hζ.stronglyMeasurable_mk.measurableSet_eq_fun hgm
  refine ⟨fun u => if hζ.mk ζ u = (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n =>
        inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1))
          (fderiv ℝ G u (EuclideanSpace.single b 1)))))⁻¹ •
        ev (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) then 1 else -1, ?_, ?_, ?_⟩
  · exact Measurable.ite hset measurable_const measurable_const
  · intro u
    dsimp only
    split_ifs <;> simp
  · filter_upwards [hζ.ae_eq_mk, hor, ae_restrict_mem hA] with u h1 h2 h3
    have hli : LinearIndependent ℝ (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) := by
      have h0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
      have h4 := h0.map' (fderiv ℝ G u : Euclid n →ₗ[ℝ] Euclid N)
        (LinearMap.ker_eq_bot.mpr (hinj u h3))
      convert h4 using 1
      funext a
      simp
    obtain ⟨hdet, -, ξu, -, hξu, huniq⟩ := Submission.cmcdt_lpi_unit_orientation_span N n _ hli
    set J := Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n =>
        inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1))
          (fderiv ℝ G u (EuclideanSpace.single b 1)))) with hJ
    have hJpos : 0 < J := Real.sqrt_pos.mpr hdet
    have hξeq : ξu = J⁻¹ • ev (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) := by
      ext α
      simp only [smul_apply, smul_eq_mul, ev,
        ContinuousAlternatingMap.apply_apply, hξu α]
      field_simp
    intro α
    split_ifs with h
    · rw [h1, h]
      simp only [smul_apply, smul_eq_mul, ev,
        ContinuousAlternatingMap.apply_apply]
      field_simp
      push_cast
      ring
    · rcases huniq (ζ u) h2 with h4 | h4
      · exact absurd (by rw [← h1, h4, hξeq]) h
      · rw [h4, neg_apply, hξu α]
        push_cast
        ring
```

## Key steps

1. z ↦ ev_z is continuous by the multilinear difference bound; v(u) = (DG(u)e_a)_a and J are Borel by measurable_fderiv_apply_const.
2. g := J^{-1}·ev∘v is strongly measurable; for a strongly measurable version ζ' of ζ, S := {ζ' = g} is Borel; s := 1 on S and −1 off S.
3. For a.e. u ∈ A, v(u) is linearly independent and cmcdt_lpi_unit_orientation_span gives J(u) > 0, ξ_u = g(u), and ζ(u) ∈ {ξ_u, −ξ_u}.
4. Case analysis on u ∈ S gives J(u)·ζ(u)(α) = s(u)·α(v(u)) for all α.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); sed -n 1,200p GMT/Ch07/Submission.lean (IMRep, IMRep.action, IMRep.Represents, IMRep.measure, IsIntegerMultiplicity, MultiVector, IsUnitOrientationOf)`
- `rg -n 'carrier ⊆|IMRep|massOn' local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json: the selected node (depth 5, max_depth 6, so new children are leaves), its parent integrality-a1 and siblings, the statuses and frozen types of the selected node's five resolved dependencies, the dependencies of every ancestor (two of them, besides this node's own not-yet-accepted span dependency, are not yet accepted), accepted theorems overlapping the supplied steps (dimred_rpd_bilipschitz_image_measure, ptd_piece_image_measurable_ae_pullback, imrep_carrier_sdiff_support_null; frozen types copied verbatim), and lean_name collisions for cmcdt_lpi_pr_imrep_in_support, cmcdt_lpi_pr_lintegral_pullback, cmcdt_lpi_pr_piece_orientation_ae, cmcdt_lpi_pr_orientation_sign, cmcdt_lpi_pr_oriented_piece_area (no node)`
- `grep -rln 'cmcdt_lpi_pr_' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib --include=*.lean (no match)`
- `grep -n in simongmt Chapter06/Mass.lean (covectorEuclideanNorm, covectorEuclideanNorm_zero, massAdmissibleOn, GeometricCurrentOn.massOn, GeometricCurrentOn.mass), Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, GeometricCurrentOn.support, isOpen_zeroRegion), Chapter06/Currents.lean (TestFormOn, GeometricCurrentOn), Chapter06/Forms.lean (Covector, DifferentialForm, IsTestForm), Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique)`
- `rg -n 'theorem hasSum_integral_iUnion|theorem measurableSet_eq_fun|theorem ae_restrict_of_ae_restrict_of_subset|theorem le_restrict_apply|theorem restrict_apply.|theorem setIntegral_congr_set|theorem lintegral_iUnion|theorem measurable_of_countable|theorem lintegral_map|theorem lintegral_smul_measure|theorem ae_eq_mk|theorem ae_eq_set' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'enorm_natCast|theorem isBoundedBilinearMap_apply|comp_aestronglyMeasurable₂|bounded_above_of_compact_support|theorem basisFun_apply|theorem LinearIndependent.map.' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'continuous_eval_const|def apply|apply_apply' Mathlib/Topology/Algebra/Module/Alternating/Topology.lean; rg -n 'norm_image_sub_le' Mathlib/Analysis/Normed/Module/Alternating/Basic.lean; rg -n 'measurable_fderiv_apply_const' Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `rg -n 'MetrizableSpace|toMetrizableSpace|pseudoMetrizableSpace' Mathlib/Topology/Metrizable/Basic.lean; rg -n 'toPseudoMetricSpace|toSeminormedAddCommGroup|toNormedAddCommGroup' Mathlib/Analysis/Normed/Operator/Basic.lean Mathlib/Analysis/Normed/Operator/NormedSpace.lean`
- `lake env lean /tmp/prsplit/Inst.lean, Inst2.lean, Inst3.lean (#synth: Covector (Euclid 3) 2 is normed via ContinuousAlternatingMap.instNormedAddCommGroup; MultiVector 3 2 is normed via ContinuousLinearMap.toNormedAddCommGroup and its topology is ContinuousLinearMap.topologicalSpace, defeq (rfl) to the norm topology; MetrizableSpace (MultiVector N n) is not synthesized but is built from a local MetricSpace; z ↦ ev_z is continuous)`
- `sed -n 1,200p nodes/root-dimension-reduction-results-a1-regular-point-density-a1-bilipsch-1804d7035f/parent-supplied-natural-proof.md (accepted proof of the reused child); python3 of nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9bda5f8762/decomposition-v1.json (parent decomposition and its reuse convention); sections of nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-655ccd9eaf/parent-supplied-natural-proof.md`
- `grep -n of /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py (_decompose and max_depth, _existing_lean_name_problem, _overlay_accepted_children, _inherited_prerequisites) and inherited.py (cited_inherited scans the whole frozen proof file, including Key steps and Reference use)`
- `git show <candidate>:GMT/Ch07/Submission.lean for the three reused theorems (d15b5cf486 imrep_carrier_sdiff_support_null, bed5b8494a ptd_piece_image_measurable_ae_pullback, 0501e07ced dimred_rpd_bilipschitz_image_measure) with #print axioms appended; lake env lean /tmp/prsplit/review/ax_*.lean (each: propext, Classical.choice, Quot.sound); sed of their accepted parent-supplied-natural-proof.md files`
- `lake env lean /tmp/prsplit/v2/ASSEMBLY.lean (the selected theorem from the eight child types and the selected node's five dependencies, all stubbed by their exact frozen types; no other sorry); /tmp/prsplit/v2/ALL.lean (five new children proven plus the assembly; no errors; only the eight stub sorry warnings; #print axioms propext, Classical.choice, Quot.sound plus sorryAx from the stubs only); /tmp/prsplit/v2/ROUNDTRIP.lean (every Lean text of this decomposition extracted verbatim from the JSON; same result); /tmp/prsplit/review/FullParent.lean (merge of the seven accepted prerequisite commits as the runtime overlays them, with only this node's not-yet-accepted span dependency stubbed; exit 0; the new children other than orientation_sign use only propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-655ccd9eaf/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-655ccd9eaf/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-655ccd9eaf/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9bda5f8762/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-bilipsch-1804d7035f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/tmp/prsplit/Stmts.lean`
- `/tmp/prsplit/Assembly.lean`
- `/tmp/prsplit/Inst.lean`
- `/tmp/prsplit/Inst2.lean`
- `/tmp/prsplit/Inst3.lean`
- `/tmp/prsplit/kids/K1.lean`
- `/tmp/prsplit/kids/K25.lean`
- `/tmp/prsplit/kids/K3.lean`
- `/tmp/prsplit/kids/K4.lean`
- `/tmp/prsplit/kids/ALL.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-e483a373f0/parent-supplied-natural-proof.md`
- `/tmp/prsplit/review/ax_imrep_carrier_sdiff_support_null.lean`
- `/tmp/prsplit/review/ax_ptd_piece_image_measurable_ae_pullback.lean`
- `/tmp/prsplit/review/ax_dimred.lean`
- `/tmp/prsplit/v2/ALL.lean`
- `/tmp/prsplit/v2/ASSEMBLY.lean`
- `/tmp/prsplit/v2/ROUNDTRIP.lean`
- `/tmp/prsplit/review/FullParent.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) carries the same Ch07 contract as the workspace. It contains no lemma giving a support-carried representation, a pulled-back integral bound for bi-Lipschitz pieces, an orientation sign for Lipschitz pieces or an oriented piece area formula. None of the five new cmcdt_lpi_pr_ names occurs in the snapshot or the DAG. Three accepted DAG theorems prove supplied steps exactly and are reused as children with their frozen types copied verbatim:
- imrep_carrier_sdiff_support_null: the null set of step 1;
- ptd_piece_image_measurable_ae_pullback: the a.e. pull-back of step 3 and Borel images;
- dimred_rpd_bilipschitz_image_measure: the measure bound of steps 3 and 10.
Each compiles at its candidate commit with only propext, Classical.choice and Quot.sound.
Library support. SimonGMT provides the current support as U ∖ zeroRegion with zeroRegion open, test forms, and HasApproximateTangentSpaceAt.unique. Mathlib provides every other tool the child proofs cite: ae_eq_set, setIntegral_congr_set, Measure.restrict_apply', Measure.map_apply, Measure.le_iff, lintegral_map, lintegral_smul_measure, ae_restrict_of_ae_restrict_of_subset, AEStronglyMeasurable.mk, StronglyMeasurable.measurableSet_eq_fun, measurable_fderiv_apply_const, ContinuousAlternatingMap.apply and norm_image_sub_le, ContinuousLinearMap.opNorm_le_bound, LinearIndependent.map', EuclideanSpace.basisFun, hasSum_integral_iUnion, lintegral_iUnion, isBoundedBilinearMap_apply and Continuous.bounded_above_of_compact_support.
Instance quirk. MultiVector N n has the CLM topology, which is defeq but not reducibly defeq to its norm topology, so MetrizableSpace must be supplied by hand. The orientation_sign proof records how.
Lean evidence. All eight child types elaborate. The selected statement compiles from the children and the selected node's dependencies. Each of the five new children has a complete Lean proof. The bundle compiles with only standard axioms plus sorryAx from the stubbed prerequisites. It also compiles on the merged real commits of the seven accepted prerequisites, where only this node's not-yet-accepted span dependency remains stubbed.
Prerequisite hygiene. No child proof file names an ancestor dependency it does not apply, so the two unaccepted ancestor dependencies of integrality-a1 and deformation_theorem-a1 never become inherited prerequisites.
