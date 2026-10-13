# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.vertex_negligible-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 8 of the supplied parent proof (parent B0.1). There it is applied to χ_εω; here it is stated for any sequence of test forms that concentrate at 0 with bounded coefficients. Book: Simon Ch. 6, 3.1 (integer multiplicity currents).
Notation: H^m := μHE[m], and |α| := covectorEuclideanNorm α.

1. (Representation.) C is integer multiplicity, so fix an IMRep R = (M_R, θ_R, ξ_R) with R.Represents C. For every k,
 C(ω_k) = ∫_{M_R} θ_R(x)·ξ_R(x)(ω_k(x)) dH^m(x) =: ∫_{M_R} F_k dH^m.
2. (A fixed ball.) A convergent real sequence is bounded, so fix R₀ with r_k ≤ R₀ for all k. Then ω_k(x) = 0 whenever |x| > R₀, since |x| > R₀ ≥ r_k.
3. (Domination.) By R.orients, for H^m-a.e. x ∈ M_R, ξ_R(x) is a unit orientation of a subspace. For such x, unit_orientation_dual (a) gives |ξ_R(x)(α)| ≤ |α| for every covector α. Then:
 - if |x| ≤ R₀, |F_k(x)| ≤ θ_R(x)·|ω_k(x)| ≤ c·θ_R(x);
 - if |x| > R₀, F_k(x) = 0.
 So |F_k| ≤ G := c·θ_R·1_{closedBall(0, R₀)} a.e. on M_R, for every k.
4. (Integrability and measurability.)
 - G is integrable on M_R: θ_R is measurable, and ∫_{M_R ∩ closedBall(0,R₀)} θ_R dH^m < ∞ by R.locallyIntegrable_mult with the compact K = closedBall(0, R₀) ⊆ ℝ^P.
 - Each F_k is a.e. strongly measurable on M_R: θ_R is measurable, ξ_R is a.e. strongly measurable for H^m⌞M_R, ω_k is continuous, and (η, α) ↦ η(α) is continuous.
5. (Pointwise limit.) Let x ≠ 0. Since r_k → 0 < |x|, we have r_k < |x| for all large k, so ω_k(x) = 0 and F_k(x) = 0 eventually. Moreover H^m({0}) = 0 because m ≥ 1: μHE[m] is a multiple of μH[m], which has no atoms in positive dimension (Measure.nullSingletonClass_hausdorff). Hence F_k → 0 a.e. on M_R.
6. By dominated convergence, C(ω_k) = ∫ F_k → ∫ 0 = 0. ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c, after `import GMT.Ch07.Submission`, in namespace GMT.Ch07 with the contract `open`s. It was compiled twice: in a standalone file, and spliced into a copy of GMT/Ch07/Submission.lean just before main_theorem. Each listed dependency was present under its exact frozen type, as an axiom standing in for the accepted or sibling declaration. `#print axioms` reports propext, Classical.choice and Quot.sound, plus exactly the declarations listed in depends_on (for reused children: their Submission names). It follows the numbered proof above.

```lean
theorem Submission.codim1_ovr_imrep_vanish_at_vertex : ∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (ωs : ℕ → TestFormOn (univ : Set (Euclid P)) m) (r : ℕ → ℝ) (c : ℝ), 1 ≤ m → IsIntegerMultiplicity C → Tendsto r atTop (𝓝 0) → (∀ (k : ℕ) (x : Euclid P), r k ≤ ‖x‖ → (ωs k : DifferentialForm (Euclid P) m) x = 0) → (∀ (k : ℕ) (x : Euclid P), covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) m) x) ≤ c) → Tendsto (fun k => C (ωs k)) atTop (𝓝 0) := by
  intro P m C ωs r c hm hIM hr hsupp hbd
  obtain ⟨R, hR⟩ := hIM
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P m
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ k, r k ≤ R₀ := by
    obtain ⟨b, hb⟩ := hr.bddAbove_range
    exact ⟨b, fun k => hb ⟨k, rfl⟩⟩
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have hK : IsCompact (closedBall (0 : Euclid P) R₀) := isCompact_closedBall 0 R₀
  have hKm : MeasurableSet (closedBall (0 : Euclid P) R₀) := measurableSet_closedBall
  have hξ : ∀ᵐ x ∂μHE[m].restrict R.carrier, ∀ γ : Covector (Euclid P) m,
      |R.orient x γ| ≤ covectorEuclideanNorm γ := by
    filter_upwards [R.orients] with x ⟨Q, _, hQ⟩ γ
    exact (hL (R.orient x) Q hQ).1 γ
  have h0null : μHE[m] ({0} : Set (Euclid P)) = 0 := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    have := Measure.nullSingletonClass_hausdorff (Euclid P) (d := (m : ℝ))
      (by exact_mod_cast hm)
    simp
  have hrep : ∀ k, C (ωs k) = ∫ x in R.carrier, (R.mult x : ℝ) *
      R.orient x ((ωs k : DifferentialForm (Euclid P) m) x) ∂μHE[m] := fun k => hR (ωs k)
  simp_rw [hrep]
  have hlim0 : (∫ x in R.carrier, (0 : ℝ) ∂μHE[m]) = 0 := integral_zero _ _
  rw [← hlim0]
  refine tendsto_integral_of_dominated_convergence
    ((closedBall (0 : Euclid P) R₀).indicator fun x => c * (R.mult x : ℝ)) ?_ ?_ ?_ ?_
  · intro k
    refine hθm.aestronglyMeasurable.mul ?_
    have hev : Continuous fun p : MultiVector P m × Covector (Euclid P) m => p.1 p.2 :=
      isBoundedBilinearMap_apply.continuous
    exact Continuous.comp_aestronglyMeasurable₂
      (g := fun (L : MultiVector P m) (v : Covector (Euclid P) m) => L v) hev
      R.aestronglyMeasurable_orient (ContDiff.continuous (ωs k).property.1.1).aestronglyMeasurable
  · refine IntegrableOn.integrable_indicator ?_ hKm
    refine Integrable.const_mul ?_ _
    show Integrable _ ((μHE[m].restrict R.carrier).restrict (closedBall (0 : Euclid P) R₀))
    rw [Measure.restrict_restrict hKm, inter_comm]
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in R.carrier ∩ closedBall (0 : Euclid P) R₀, ‖(R.mult x : ℝ)‖ₑ ∂μHE[m] < ∞
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.2 (R.locallyIntegrable_mult _ hK (subset_univ _))
  · intro k
    filter_upwards [hξ] with x hx
    by_cases hxK : x ∈ closedBall (0 : Euclid P) R₀
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs, mul_comm c]
      exact mul_le_mul_of_nonneg_left ((hx _).trans (hbd k x)) (Nat.cast_nonneg _)
    · rw [indicator_of_notMem hxK]
      have hxr : r k ≤ ‖x‖ := by
        rw [mem_closedBall, dist_zero_right, not_le] at hxK
        exact (hR₀ k).trans hxK.le
      rw [hsupp k x hxr, map_zero, mul_zero, norm_zero]
  · have hae : ∀ᵐ x ∂μHE[m].restrict R.carrier, x ≠ 0 := by
      apply ae_restrict_of_ae
      rw [ae_iff]
      simpa using h0null
    filter_upwards [hae] with x hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hev : ∀ᶠ k in atTop, r k < ‖x‖ := hr.eventually (gt_mem_nhds hxpos)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with k hk
    rw [hsupp k x hk.le, map_zero, mul_zero]
```

## Key steps

1. Write C(ω_k) as the integral of θ_R·⟨ω_k, ξ_R⟩ over the carrier of an IMRep R of C.
2. unit_orientation_dual bounds the integrands by c·θ_R on a fixed closed ball, where θ_R is integrable (R.locallyIntegrable_mult).
3. The integrands vanish eventually at every x ≠ 0, and H^m({0}) = 0 since m ≥ 1; dominated convergence gives the limit 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `cat GMT/Ch07/Contract.lean (IMRep, IsIntegerMultiplicity, IsConeCurrent, blowUp, dilation, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, regularSet, HasMassDensity)`
- `grep -n 'VanishesOn|def zeroRegion|def support|isOpen_zeroRegion|structure GeometricCurrentOn|abbrev TestFormOn|IsTestForm|IsSmoothForm|covectorEuclideanNorm|testFormEuclideanSupNorm' simongmt/Poincare/SimonGMT/Chapter06/{CurrentLocalEquality,Currents,Forms,Mass,FormSupNorm}.lean`
- `rg -n 'euclideanHausdorffMeasure_smul₀|nullSingletonClass_hausdorff|exists_isSubordinate|one_of_mem_closedBall|support_eq|tsupport_eq|tendsto_integral_of_dominated_convergence|setIntegral_ge_of_const_le_real|setIntegral_mono_set|IntegrableOn.of_bound|ENNReal.tsum_geometric|exists_nat_pow_near|Tendsto.bddAbove_range|ContinuousAlternatingMap.apply' <snapshot>/mathlib/Mathlib`
- `rg -c 'codim1_ovr_' <snapshot> (no match); grep each of the 7 new lean_names in dag.json (no match); git grep -l 'codim1_ovr_' over all 1662 distinct ref objects (no match)`
- `python3 over dag.json: accepted nodes whose lean_statement mentions IsEmbeddedSubmanifold, tangentSpace or IsOrientation; nodes with IsConeCurrent and support; IMRep/IsIntegerMultiplicity with Tendsto; status, frozen type, candidate commit and parent handoff of the 5 reused names; children of simons_regular_cone-a1`
- `git show <commit> -- GMT/Ch07/Submission.lean for 44ef61f79e21 (dtc_vanish_off_support: smooth partition of unity), 52115c22ec2d (cone_current_apply_dilation_pullback), d626082a69a0 (chart_tangentSpace_eq_range_fderiv), a5ceace526bc (dpf_pb_imrep_pullback_integral_tendsto: IMRep dominated convergence)`
- `runtime.py (_decompose, _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff) and speculation.py contract (a parent's prerequisites are its children plus its depends_on)`
- `lean -DautoImplicit=false /tmp/ovr-split-check/{Types,Assembly,SkelC3,C1C2,C4,C5,C6,C7,Full,SubmissionCopy}.lean with LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b7ab3fcecc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1-27e5a07a68/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/speculation.py`
- `/tmp/ovr-split-check/Full.lean`
- `/tmp/ovr-split-check/SubmissionCopy.lean`

Pins match. The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library.
- SimonGMT Chapter06 supplies GeometricCurrentOn, TestFormOn, VanishesOn, the open zeroRegion, support = U ∖ zeroRegion, and covectorEuclideanNorm.
- SimonGMT has no continuity or homogeneity lemma for covectorEuclideanNorm, and no local-to-global gluing lemma for currents. The children prove these inline.
- The snapshot Mathlib has every library lemma the children use:
  - Measure.euclideanHausdorffMeasure_smul₀ (Geometry/Euclidean/Volume/Measure.lean:152);
  - nullSingletonClass_hausdorff (MeasureTheory/Measure/Hausdorff.lean:615);
  - SmoothPartitionOfUnity.exists_isSubordinate (Geometry/Manifold/PartitionOfUnity.lean:555);
  - ContDiffBump.one_of_mem_closedBall, support_eq and tsupport_eq (Analysis/Calculus/BumpFunction/Basic.lean:137–157);
  - tendsto_integral_of_dominated_convergence (MeasureTheory/Integral/DominatedConvergence.lean:57);
  - setIntegral_mono_set and setIntegral_ge_of_const_le_real (MeasureTheory/Integral/Bochner/Set.lean:737, 798);
  - IntegrableOn.of_bound (MeasureTheory/Integral/IntegrableOn.lean:174);
  - ENNReal.tsum_geometric (Analysis/SpecificLimits/Basic.lean:402);
  - exists_nat_pow_near (Algebra/Order/Archimedean/Basic.lean:195).
DAG.
- Five accepted declarations are reused with byte-identical frozen types: cone_current_apply_dilation_pullback (52115c22ec2d), chart_tangentSpace_eq_range_fderiv (d626082a69a0), dor_ims_unitOrientation_dual (9c8432cb0101), rsdic_unitOrientation_eq_or_eq_neg (fe95347baaed) and dimred_rpd_submanifold_density_one (e8842d90b78f).
- Unaccepted nodes owned by other parents cannot be shared: idtp_tpf_cone_support_smul and idtp_ccd_cone_support_smul (decomposing) have the content of cone_support_smul. So that child gets the fresh name codim1_ovr_cone_support_smul.
- The 7 new codim1_ovr_ names are free in dag.json, the snapshot, SimonGMT and all git refs.
- This node's own prerequisites stay available to its glue (speculation.contract = children + depends_on): codim1_density_one_regular_local_rep, dtc_vanish_off_support and dor_ims_unitOrientation_dual.
Lean.
- Types.lean elaborates all 12 child types.
- Assembly.lean proves the selected frozen type from the frozen child types and this node's prerequisites, all given as axioms.
- Each new child has a complete Lean proof that uses exactly its listed dependencies. These proofs are attached to the child proofs.
- Full.lean, and SubmissionCopy.lean (the same block spliced into a copy of Submission.lean before main_theorem), compile without errors.
- #print axioms of the selected theorem lists propext, Classical.choice and Quot.sound, plus the 7 frozen prerequisites: the 5 reused declarations, codim1_density_one_regular_local_rep and dtc_vanish_off_support.
