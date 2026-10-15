# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1.open_piece-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent fact (F2) ("Open pieces") of the supplied proof of codim1_density_one_regular_local_rep, used there in step 7(i)–(ii). Book: Simon Ch. 2, §4, 4.1–4.3 (chapter-02.txt lines 850–871: local representations ψ : V → W with ψ(V) = W ∩ M, ψ proper, Dψ of maximal rank; T_yM = {γ'(0) : γ a C¹ curve in M with γ(0) = y}).
Departure from the parent text, stated explicitly. Part (a) is the parent's chart restriction (V ∩ ψ⁻¹(O), W ∩ O, ψ). For part (b) the parent compared the two charts through chart_tangent_space, which needs r ≥ 1 and w ∈ N. Here (b) is proved directly from the definition of tangentSpace by reparametrizing curves; this works for every r ∈ ℕ and every w ∈ O (for w ∉ N both sides are empty) and needs no dependency.

Notation. tangentSpace(M, w) is the set of v ∈ ℝ^P for which there is γ : ℝ → ℝ^P that is C¹ on (−1, 1) (ContDiffOn ℝ 1 γ (Ioo (−1) 1)), maps (−1, 1) into M, satisfies γ(0) = w and has derivative v at 0 (HasDerivAt γ v 0). Such γ is called a witness for v ∈ tangentSpace(M, w).

Proof. Fix P, r, d, N with IsEmbeddedSubmanifold r d N, and an open O ⊆ ℝ^P.
1. (Part (a): the restricted chart.) Let w ∈ N ∩ O. As w ∈ N, the definition of IsEmbeddedSubmanifold r d N gives open V ⊆ ℝ^d and W ⊆ ℝ^P with w ∈ W and ψ : ℝ^d → ℝ^P such that ψ is C^r on V, ψ is injective on V, ψ(V) = W ∩ N, V ∩ ψ⁻¹(K) is compact for every compact K ⊆ W, and Dψ(z) (fderiv ℝ ψ z) is injective for every z ∈ V. Put V' := V ∩ ψ⁻¹(O) and W' := W ∩ O. We verify every clause of the definition for the point w, the set N ∩ O and the triple (V', W', ψ).
 (1a) V' is open: a C^r map on V (r ≥ 0) is continuous on V, and for a map continuous on the open set V the set V ∩ ψ⁻¹(O) is open because O is open.
 (1b) W' is open as the intersection of two open sets, and w ∈ W' because w ∈ W and w ∈ O.
 (1c) ψ is C^r on V' and injective on V', by restriction from V ⊇ V'.
 (1d) ψ(V') = ψ(V ∩ ψ⁻¹(O)) = ψ(V) ∩ O = (W ∩ N) ∩ O = W' ∩ (N ∩ O).
 (1e) Let K ⊆ W' be compact. Then K ⊆ O, so ψ⁻¹(K) ⊆ ψ⁻¹(O) and V' ∩ ψ⁻¹(K) = V ∩ ψ⁻¹(K). Since K ⊆ W is compact, this set is compact by the properness clause of the chart (V, W, ψ).
 (1f) For z ∈ V' we have z ∈ V, so Dψ(z) is injective (it is the same derivative of the same map ψ).
 Since w ∈ N ∩ O was arbitrary, IsEmbeddedSubmanifold r d (N ∩ O) holds.
2. (Part (b), inclusion ⊆.) Let w ∈ O and v ∈ tangentSpace(N ∩ O, w) with witness γ. Since γ maps (−1, 1) into N ∩ O ⊆ N, the same γ is a witness for v ∈ tangentSpace(N, w).
3. (Part (b), inclusion ⊇: choice of a small parameter.) Let w ∈ O and v ∈ tangentSpace(N, w) with witness γ: γ is C¹ on (−1, 1), γ((−1, 1)) ⊆ N, γ(0) = w and HasDerivAt γ v 0. Being differentiable at 0, γ is continuous at 0. As γ(0) = w ∈ O and O is open, γ⁻¹(O) is a neighbourhood of 0, so there is δ > 0 with γ(t) ∈ O whenever |t| < δ. Put ε := min(δ/2, 1/2). Then 0 < ε, ε < δ and ε < 1.
4. (The reparametrization.) Define h : ℝ → ℝ by h(t) := ε·sin(t/ε), and γ̃ := γ ∘ h.
 (4a) |h(t)| = ε·|sin(t/ε)| ≤ ε for every t ∈ ℝ. In particular h maps (−1, 1) into [−ε, ε] ⊆ (−1, 1), because ε < 1.
 (4b) h is C^∞ (composition of t ↦ t/ε, sin and multiplication by ε), h(0) = ε·sin 0 = 0, and by the chain rule h has derivative ε·cos(0/ε)·(1/ε) = 1 at 0.
5. (γ̃ is a witness for v ∈ tangentSpace(N ∩ O, w).)
 (5a) γ̃ is C¹ on (−1, 1): γ is C¹ on (−1, 1), h is C¹ on ℝ and maps (−1, 1) into (−1, 1) by (4a), so the composite is C¹ on (−1, 1).
 (5b) γ̃ maps (−1, 1) into N ∩ O: for t ∈ (−1, 1), h(t) ∈ (−1, 1) by (4a), so γ(h(t)) ∈ N; and |h(t)| ≤ ε < δ, so γ(h(t)) ∈ O by step 3.
 (5c) γ̃(0) = γ(h(0)) = γ(0) = w.
 (5d) γ has derivative v at h(0) = 0 and h has derivative 1 at 0, so by the chain rule γ̃ = γ ∘ h has derivative 1·v = v at 0, i.e. HasDerivAt γ̃ v 0.
 Hence v ∈ tangentSpace(N ∩ O, w).
6. (Conclusion.) Steps 2–5 give tangentSpace(N ∩ O, w) = tangentSpace(N, w) for every w ∈ O. Together with step 1 this proves both conjuncts. ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 (Mathlib 25730c7c) against the workspace build of GMT.Ch07.Submission at b4d606db, after `import GMT.Ch07.Submission` with the contract's namespace GMT.Ch07 and `open`s. It exits 0 with no `sorry`, and `#print axioms` lists only propext, Classical.choice and Quot.sound. It follows the numbered proof above.

```lean
theorem Submission.codim1_dolr_embedded_inter_open : ∀ (P r d : ℕ) (N O : Set (Euclid P)), IsEmbeddedSubmanifold r d N → IsOpen O → IsEmbeddedSubmanifold r d (N ∩ O) ∧ ∀ w ∈ O, tangentSpace (N ∩ O) w = tangentSpace N w := by
  intro P r d N O hN hO
  constructor
  · intro w hw
    obtain ⟨V, W, ψ, hV, hW, hwW, hψ, hinj, himg, hprop, hder⟩ := hN w hw.1
    refine ⟨V ∩ ψ ⁻¹' O, W ∩ O, ψ, hψ.continuousOn.isOpen_inter_preimage hV hO, hW.inter hO,
      ⟨hwW, hw.2⟩, hψ.mono inter_subset_left, hinj.mono inter_subset_left, ?_, ?_, ?_⟩
    · rw [image_inter_preimage, himg]
      ext z
      simp only [mem_inter_iff]
      tauto
    · intro K hK hKc
      have : V ∩ ψ ⁻¹' O ∩ ψ ⁻¹' K = V ∩ ψ ⁻¹' K := by
        ext z
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨⟨h1, (hK h3).2⟩, h3⟩
      rw [this]
      exact hprop K (hK.trans inter_subset_left) hKc
    · intro z hz
      exact hder z hz.1
  · intro w hwO
    ext v
    constructor
    · rintro ⟨γ, hγ, hmaps, h0, hd⟩
      exact ⟨γ, hγ, fun t ht => (hmaps ht).1, h0, hd⟩
    · rintro ⟨γ, hγ, hmaps, h0, hd⟩
      have hcont : ContinuousAt γ 0 := hd.continuousAt
      have hO' : γ ⁻¹' O ∈ 𝓝 (0 : ℝ) := hcont.preimage_mem_nhds (hO.mem_nhds (h0 ▸ hwO))
      obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hO'
      set ε : ℝ := min (δ / 2) (1 / 2) with hε_def
      have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
      have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
      have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      set h : ℝ → ℝ := fun t => ε * Real.sin (t / ε) with hh_def
      have hbound : ∀ t, |h t| ≤ ε := by
        intro t
        simp only [hh_def, abs_mul, abs_of_pos hε]
        exact mul_le_of_le_one_right hε.le (Real.abs_sin_le_one _)
      have hmapsI : MapsTo h (Ioo (-1) 1) (Ioo (-1) 1) := by
        intro t _
        have h1 := abs_le.mp (hbound t)
        rw [mem_Ioo]
        constructor <;> linarith [h1.1, h1.2]
      have hh0 : h 0 = 0 := by simp [hh_def]
      have hh' : HasDerivAt h 1 0 := by
        have h2 : HasDerivAt (fun t : ℝ => ε * Real.sin (t / ε))
            (ε * (Real.cos (0 / ε) * (1 / ε))) 0 :=
          (((hasDerivAt_id' (0 : ℝ)).div_const ε).sin).const_mul ε
        have h3 : ε * (Real.cos (0 / ε) * (1 / ε)) = 1 := by
          rw [zero_div, Real.cos_zero, one_mul]
          field_simp
        rw [h3] at h2
        exact h2
      refine ⟨γ ∘ h, ?_, ?_, ?_, ?_⟩
      · have hhd : ContDiff ℝ 1 h := by
          simp only [hh_def]
          fun_prop
        exact hγ.comp hhd.contDiffOn hmapsI
      · intro t ht
        refine ⟨hmaps (hmapsI ht), ?_⟩
        have : h t ∈ ball (0 : ℝ) δ := by
          rw [mem_ball, dist_zero_right, Real.norm_eq_abs]
          exact lt_of_le_of_lt (hbound t) hεδ
        exact hδs this
      · simp [hh0, h0]
      · have hd' : HasDerivAt γ v (h 0) := by rw [hh0]; exact hd
        simpa using hd'.scomp 0 hh'
```

## Key steps

1. Part (a): restrict a chart (V, W, ψ) of N at w ∈ N ∩ O to (V ∩ ψ⁻¹(O), W ∩ O, ψ); openness (ψ continuous on V), ψ(V ∩ ψ⁻¹(O)) = (W ∩ O) ∩ (N ∩ O), properness (V ∩ ψ⁻¹(O) ∩ ψ⁻¹(K) = V ∩ ψ⁻¹(K) for K ⊆ O), and injectivity of ψ and Dψ all restrict.
2. Part (b) ⊆: a witness curve into N ∩ O is a witness curve into N.
3. Part (b) ⊇: choose δ > 0 with γ(t) ∈ O for |t| < δ, ε := min(δ/2, 1/2), h(t) := ε·sin(t/ε); then |h| ≤ ε < min(δ, 1), h(0) = 0, h'(0) = 1.
4. γ ∘ h is C¹ on (−1, 1), maps (−1, 1) into N ∩ O, equals w at 0 and has derivative h'(0)·v = v at 0 (chain rule), so v ∈ tangentSpace(N ∩ O, w).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, regularSet, HasMassDensity, unitBallVolume, MultiVector)`
- `grep -n 'def support|def zeroRegion|isOpen_zeroRegion|VanishesOn|def massOn|massAdmissibleOn|structure GeometricCurrentOn|testFormOnSubmodule|abbrev Covector|def covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass,Forms}.lean`
- `python3 scans of dag.json: lean_statement mentions IsEmbeddedSubmanifold, IsOrientation, regularSet, tangentSpace, support, massOn; children of regular_point_density-a1, simons_regular_cone-a1, imrep_mass_and_support-a1, cone_constant_density_planar-a1; status and candidate_commit of dimred_rpd_submanifold_density_one, dimred_rpd_massOn_eq_mult_measure, dimred_rpd_embedded_locally_closed, dimred_rpd_near_isometric_chart, dor_ims_unitOrientation_dual, chart_tangentSpace_eq_range_fderiv, dimred_rpd_bilipschitz_image_measure, dor_ims_support_of_massOn_eq, dimred_regular_point_density, idtp_ccd_regular_point_support, codim1_massOn_eq_lintegral_of_oriented_rep`
- `grep -rln IsEmbeddedSubmanifold local-references/123e8435b4a2469b/project; grep -rn 'theorem.*inter_open|theorem.*tangentSpace_inter|theorem.*support_inter' local-references/123e8435b4a2469b/project; grep -rn 'theorem .*support.*rep|theorem .*mem_support' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn 'setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|setIntegral_eq_zero_of_forall_eq_zero|image_eq_zero_of_notMem_tsupport|IsOpen.closure_inter|ContinuousOn.isOpen_inter_preimage|HasDerivAt.scomp|ContDiffOn.comp|closure_ball|tendsto_nhds_unique|integral_const_mul' Mathlib`
- `runtime.py _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, _wait_for_accepted_dependencies; store.py ensure; models.py Subproblem/Decomposition; lean_contract.py validate_lean_statement`
- `git for-each-ref --format='%(objectname)' | sort -u | xargs -n 100 sh -c 'git grep -l -E "codim1_dolr_(embedded_inter_open|rep_hasMassDensity|rep_support_inter)" "$@" -- GMT' _ (positive control: Submission.dimred_rpd_submanifold_density_one)`
- `lean -DautoImplicit=false /tmp/dolr-split/check/Types2.lean, Children2.lean, Assembly2.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `book: chapter-02.txt 850-871; chapter-03.txt 290-316; chapter-06.txt 225-233 and 290-305; chapter-07.txt 588-600`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/RCLike/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b47a776447/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-mass-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-locally-closed-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dolr-split/check/Types2.lean`
- `/tmp/dolr-split/check/Children2.lean`
- `/tmp/dolr-split/check/Assembly2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and the pinned Mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). So the selected frozen type and the definitions it uses (regularSet, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, HasMassDensity) are unchanged.
Library.
- SimonGMT Chapter06 defines T.support = U \ T.zeroRegion, where zeroRegion is the union of the open W with compact closure inside U on which T vanishes (CurrentLocalEquality.lean). It defines T.massOn W as a supremum of ofReal T(ω) over massAdmissibleOn (Mass.lean), and TestFormOn as the smooth compactly supported forms with tsupport in U (Currents.lean).
- SimonGMT has no lemma relating the support or the mass to a local representation m[[M]]. The snapshot project has no embedded-submanifold lemmas beyond the contract definitions (no match).
- The pinned Mathlib supplies every tool the child and glue proofs use (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_eq_zero_of_forall_eq_zero, image_eq_zero_of_notMem_tsupport, IsOpen.closure_inter, ContinuousOn.isOpen_inter_preimage, HasDerivAt.scomp, ContDiffOn.comp, closure_ball, tendsto_nhds_unique, ENNReal.Tendsto.const_mul).
DAG.
- The parent handoff listed dimred_rpd_submanifold_density_one and dimred_rpd_massOn_eq_mult_measure as unaccepted, reusable by child sessions once accepted. Both are now accepted (candidate commits e8842d90b78f and 5fcaddaa05c1), as is dimred_rpd_embedded_locally_closed (6da66b1edf6f). Their frozen types are copied byte-for-byte, so they are reused with no new DAG node (runtime _existing_lean_name_problem / _accepted_checkpoint).
- idtp_ccd_regular_point_support and codim1_massOn_eq_lintegral_of_oriented_rep remain unaccepted in other branches and are not used.
- The 3 new codim1_dolr_ names are free in dag.json (974 nodes), GMT/, SimonGMT and all 1734 ref tips (corrected git grep, positive control 6 hits).
Lean.
- Types2.lean elaborates all 6 child types (exit 0).
- Assembly2.lean proves the selected frozen type from open_piece, rep_density, rep_support and locally_closed as axioms (exit 0; #print axioms: propext, Classical.choice, Quot.sound and those 4).
- Children2.lean proves the 3 new children from the 3 accepted declarations, with no sorry (exit 0).
