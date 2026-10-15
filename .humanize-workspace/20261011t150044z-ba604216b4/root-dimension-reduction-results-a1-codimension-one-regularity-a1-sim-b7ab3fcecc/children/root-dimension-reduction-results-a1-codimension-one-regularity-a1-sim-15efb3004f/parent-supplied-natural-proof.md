# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.vertex_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 8 and 9 of the supplied parent proof (parent B0.1 and B10b). Step 8 is used through the sibling vertex_negligible.
Notation: H^m := μHE[m], ⟨α, η⟩ := η(α), and |α| := covectorEuclideanNorm α.
Fix ω ∈ 𝒟^m(ℝ^P) and put K := tsupport ω, a compact set.

1. (Bounds.)
 - |·| is continuous: it is the square root of a finite sum of squares of the continuous evaluations α ↦ α(e_{I(0)}, …, e_{I(m−1)}).
 - |·| is absolutely homogeneous: |aα| = |a|·|α|, because each evaluation scales by a.
 - x ↦ |ω(x)| is continuous with compact support, so |ω(x)| ≤ S for some S and all x.
2. (Cut-offs.) For k ∈ ℕ let ε_k := 1/(k+1), and let χ_k : ℝ^P → [0, 1] be the smooth bump ContDiffBump centred at 0 with radii ε_k < 2ε_k. Then χ_k = 1 on closedBall(0, ε_k) and support χ_k = B_{2ε_k}(0).
 - ω_k^in := χ_kω and ω_k^out := (1 − χ_k)ω are smooth with support in K, so they lie in 𝒟^m(ℝ^P).
 - ω = ω_k^in + ω_k^out, so C(ω) = C(ω_k^in) + C(ω_k^out) by linearity.
3. (Step 8: C(ω_k^in) → 0.) Apply vertex_negligible with r_k := 2ε_k → 0 and c := S.
 - If |x| ≥ 2ε_k then χ_k(x) = 0, so ω_k^in(x) = 0.
 - |ω_k^in(x)| = χ_k(x)·|ω(x)| ≤ S.
 Hence C(ω_k^in) → 0.
4. (The outer parts.) (1 − χ_k)ω vanishes on the open ball B_{ε_k}(0) ∋ 0, so 0 ∉ tsupport ω_k^out. By hypothesis,
 C(ω_k^out) = ∫_M ⟨(1 − χ_k)ω, ξ⟩ dH^m = ∫_M (1 − χ_k(x))·ξ(x)(ω(x)) dH^m(x) =: ∫_M G_k dH^m.
5. (Step 9: dominated convergence on M.)
 - G_k is continuous on the Borel set M, hence a.e. strongly measurable for H^m⌞M.
 - For x ∈ M ∩ K, |G_k(x)| ≤ |1 − χ_k(x)|·|ξ(x)(ω(x))| ≤ |ω(x)| ≤ S, using 0 ≤ χ_k ≤ 1 and the hypothesis on ξ. For x ∈ M ∖ K, ω(x) = 0, so G_k(x) = 0.
 - So |G_k| ≤ S·1_K on M. This bound is integrable for H^m⌞M because H^m(M ∩ K) < ∞.
 - For x ∈ M we have x ≠ 0 (0 ∉ M). Once 2ε_k < |x|, χ_k(x) = 0 and G_k(x) = ξ(x)(ω(x)).
 Hence ∫_M G_k dH^m → ∫_M ⟨ω, ξ⟩ dH^m.
6. Therefore C(ω) = C(ω_k^in) + C(ω_k^out) → 0 + ∫_M ⟨ω, ξ⟩ dH^m. The left side does not depend on k, so by uniqueness of limits C(ω) = ∫_M ⟨ω(x), ξ(x)⟩ dH^m(x). ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c, after `import GMT.Ch07.Submission`, in namespace GMT.Ch07 with the contract `open`s. It was compiled twice: in a standalone file, and spliced into a copy of GMT/Ch07/Submission.lean just before main_theorem. Each listed dependency was present under its exact frozen type, as an axiom standing in for the accepted or sibling declaration. `#print axioms` reports propext, Classical.choice and Quot.sound, plus exactly the declarations listed in depends_on (for reused children: their Submission names). It follows the numbered proof above.

```lean
theorem Submission.codim1_ovr_extend_rep_across_vertex : ∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P m), 1 ≤ m → IsIntegerMultiplicity C → MeasurableSet M → (0 : Euclid P) ∉ M → ContinuousOn ξ M → (∀ x ∈ M, ∀ α : Covector (Euclid P) m, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, (0 : Euclid P) ∉ tsupport (ω : DifferentialForm (Euclid P) m) → C ω = ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, C ω = ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] := by
  intro P m C M ξ hm hIM hMm h0M hξc hξb hfin hoff ω
  set ω₀ : DifferentialForm (Euclid P) m := (ω : DifferentialForm (Euclid P) m) with hω₀
  have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω₀ := ω.property.1.1
  have hωc : HasCompactSupport ω₀ := ω.property.1.2
  -- the Euclidean covector norm is continuous and absolutely homogeneous
  have hnc : Continuous fun α : Covector (Euclid P) m => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
        (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))).continuous).pow 2
    · exact continuous_const
  have hsmul : ∀ (a : ℝ) (α : Covector (Euclid P) m),
      covectorEuclideanNorm (a • α) = |a| * covectorEuclideanNorm α := by
    intro a α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg a), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]; ring
    · simp
  obtain ⟨S, hS⟩ : ∃ S, ∀ x, covectorEuclideanNorm (ω₀ x) ≤ S := by
    obtain ⟨S, hS⟩ := (hnc.comp hωs.continuous).bounded_above_of_compact_support
      (hωc.comp_left (covectorEuclideanNorm_zero P m))
    exact ⟨S, fun x => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hS x)⟩
  -- cut-offs χₖ = 1 on closedBall 0 εₖ, supported in ball 0 (2εₖ)
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  let χ : ℕ → ContDiffBump (0 : Euclid P) := fun k => ⟨ε k, 2 * ε k, hε k, by linarith [hε k]⟩
  have hin : ∀ k, (fun x => χ k x • ω₀ x) ∈ TestFormOn (univ : Set (Euclid P)) m := by
    intro k
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => χ k x • ω₀ x) :=
      ((χ k).contDiff (n := ⊤)).smul hωs
    have h2 : HasCompactSupport (fun x => χ k x • ω₀ x) :=
      hωc.mono (support_smul_subset_right (fun x => χ k x) ω₀)
    exact ⟨⟨h1, h2⟩, subset_univ _⟩
  have hout : ∀ k, (fun x => (1 - χ k x) • ω₀ x) ∈ TestFormOn (univ : Set (Euclid P)) m := by
    intro k
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (1 - χ k x) • ω₀ x) :=
      (contDiff_const.sub ((χ k).contDiff (n := ⊤))).smul hωs
    have h2 : HasCompactSupport (fun x => (1 - χ k x) • ω₀ x) :=
      hωc.mono (support_smul_subset_right (fun x => 1 - χ k x) ω₀)
    exact ⟨⟨h1, h2⟩, subset_univ _⟩
  let ωin : ℕ → TestFormOn (univ : Set (Euclid P)) m := fun k => ⟨_, hin k⟩
  let ωout : ℕ → TestFormOn (univ : Set (Euclid P)) m := fun k => ⟨_, hout k⟩
  have hsplit : ∀ k, C ω = C (ωin k) + C (ωout k) := by
    intro k
    have hsum : ω = ωin k + ωout k := by
      apply Subtype.ext; funext x
      show ω₀ x = χ k x • ω₀ x + (1 - χ k x) • ω₀ x
      rw [← add_smul]; simp
    rw [hsum]; exact map_add (C.toCurrent : TestFormOn (univ : Set (Euclid P)) m →ₗ[ℝ] ℝ) _ _
  -- step 8: C(χₖω) → 0
  have h1 : Tendsto (fun k => C (ωin k)) atTop (𝓝 0) := by
    refine Submission.codim1_ovr_imrep_vanish_at_vertex P m C ωin (fun k => 2 * ε k) S hm hIM ?_ ?_ ?_
    · have : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this.const_mul 2
    · intro k x hx
      show χ k x • ω₀ x = 0
      have hxs : x ∉ support (χ k) := by
        rw [(χ k).support_eq, mem_ball, dist_zero_right, not_lt]; exact hx
      rw [notMem_support.1 hxs, zero_smul]
    · intro k x
      show covectorEuclideanNorm (χ k x • ω₀ x) ≤ S
      rw [hsmul, abs_of_nonneg (χ k).nonneg]
      calc χ k x * covectorEuclideanNorm (ω₀ x) ≤ 1 * covectorEuclideanNorm (ω₀ x) :=
            mul_le_mul_of_nonneg_right (χ k).le_one (covectorEuclideanNorm_nonneg _)
        _ ≤ S := by rw [one_mul]; exact hS x
  -- step 9: C((1 − χₖ)ω) = ∫_M (1 − χₖ)⟨ω, ξ⟩
  have h2 : ∀ k, C (ωout k) = ∫ x in M, (1 - χ k x) * ξ x (ω₀ x) ∂μHE[m] := by
    intro k
    rw [hoff (ωout k) ?_]
    · refine setIntegral_congr_fun hMm fun x _ => ?_
      show ξ x ((1 - χ k x) • ω₀ x) = _
      rw [map_smul, smul_eq_mul]
    · intro h0
      have hnhds : ball (0 : Euclid P) (ε k) ∈ 𝓝 (0 : Euclid P) := ball_mem_nhds 0 (hε k)
      have hzero : ∀ x ∈ ball (0 : Euclid P) (ε k), (1 - χ k x) • ω₀ x = 0 := by
        intro x hx
        rw [(χ k).one_of_mem_closedBall (ball_subset_closedBall hx), sub_self, zero_smul]
      exact (notMem_tsupport_iff_eventuallyEq.2
        (Filter.eventually_of_mem hnhds hzero)) h0
  -- dominated convergence on M
  have hK : IsCompact (tsupport ω₀) := hωc
  have h3 : Tendsto (fun k => ∫ x in M, (1 - χ k x) * ξ x (ω₀ x) ∂μHE[m]) atTop
      (𝓝 (∫ x in M, ξ x (ω₀ x) ∂μHE[m])) := by
    refine tendsto_integral_of_dominated_convergence
      ((tsupport ω₀).indicator fun _ => S) ?_ ?_ ?_ ?_
    · intro k
      refine (((continuousOn_const (c := (1 : ℝ))).sub (χ k).continuous.continuousOn).mul
        (hξc.clm_apply hωs.continuous.continuousOn)).aestronglyMeasurable hMm
    · refine IntegrableOn.integrable_indicator ?_ hK.isClosed.measurableSet
      show IntegrableOn (fun _ => S) (tsupport ω₀) (μHE[m].restrict M)
      refine integrableOn_const ?_
      rw [Measure.restrict_apply hK.isClosed.measurableSet, inter_comm]
      exact hfin _ hK
    · intro k
      refine (ae_restrict_iff' hMm).2 (Eventually.of_forall fun x hx => ?_)
      by_cases hxK : x ∈ tsupport ω₀
      · rw [indicator_of_mem hxK, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have h01 : |1 - χ k x| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [(χ k).nonneg (x := x), (χ k).le_one (x := x)]
        calc |1 - χ k x| * |ξ x (ω₀ x)| ≤ 1 * covectorEuclideanNorm (ω₀ x) :=
              mul_le_mul h01 (hξb x hx _) (abs_nonneg _) zero_le_one
          _ ≤ S := by rw [one_mul]; exact hS x
      · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, mul_zero,
          norm_zero]
    · refine (ae_restrict_iff' hMm).2 (Eventually.of_forall fun x hx => ?_)
      have hx0 : x ≠ 0 := fun h => h0M (h ▸ hx)
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hev : ∀ᶠ k in atTop, 2 * ε k < ‖x‖ := by
        have hε' : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
        have : Tendsto (fun k => 2 * ε k) atTop (𝓝 0) := by simpa using hε'.const_mul 2
        exact this.eventually (gt_mem_nhds hxpos)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with k hk
      have hxs : x ∉ support (χ k) := by
        rw [(χ k).support_eq, mem_ball, dist_zero_right, not_lt]; exact hk.le
      rw [notMem_support.1 hxs, sub_zero, one_mul]
  have h4 : Tendsto (fun k => C (ωin k) + C (ωout k)) atTop
      (𝓝 (0 + ∫ x in M, ξ x (ω₀ x) ∂μHE[m])) := by
    refine h1.add ?_
    simp_rw [h2]; exact h3
  rw [zero_add] at h4
  have h5 : (fun k => C (ωin k) + C (ωout k)) = fun _ => C ω := funext fun k => (hsplit k).symm
  rw [h5] at h4
  exact tendsto_nhds_unique tendsto_const_nhds h4
```

## Key steps

1. Split ω = χ_kω + (1 − χ_k)ω with smooth bumps χ_k = 1 near 0 and supported in B_{2/(k+1)}(0).
2. vertex_negligible gives C(χ_kω) → 0.
3. The hypothesis gives C((1 − χ_k)ω) = ∫_M (1 − χ_k)⟨ω, ξ⟩, which tends to ∫_M ⟨ω, ξ⟩ by dominated convergence, since 0 ∉ M and H^m(M ∩ tsupport ω) < ∞.

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
