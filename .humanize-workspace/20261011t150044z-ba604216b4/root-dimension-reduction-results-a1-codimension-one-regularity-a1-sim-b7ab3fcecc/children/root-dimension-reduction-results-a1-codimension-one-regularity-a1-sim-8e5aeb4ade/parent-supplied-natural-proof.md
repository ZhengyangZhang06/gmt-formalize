# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.submanifold_local-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 2 and fact (F2) of the supplied parent proof. Book: Simon Ch. 2, §4, (4.1) (embedded submanifolds and local representations) and the definition of T_yM.
Terminology. A chart of N at y is a triple (V, W, ψ) as in IsEmbeddedSubmanifold r d N:
- V ⊆ ℝ^d and W ⊆ ℝ^P are open, with y ∈ W;
- ψ is C^r and injective on V, with ψ(V) = W ∩ N;
- V ∩ ψ⁻¹(K) is compact for every compact K ⊆ W;
- Dψ(z) is injective for every z ∈ V.

1. (M is an embedded submanifold.) Let y ∈ M. Choose an open O ∋ y as in the hypothesis and a chart (V, W, ψ) of M ∩ O at y (y ∈ M ∩ O). Then (V, W ∩ O, ψ) is a chart of M at y:
 - V is open, W ∩ O is open, and y ∈ W ∩ O;
 - ψ is C^r and injective on V, and Dψ(z) is injective for z ∈ V, unchanged;
 - ψ(V) = W ∩ (M ∩ O) = (W ∩ O) ∩ M;
 - every compact K ⊆ W ∩ O satisfies K ⊆ W, so V ∩ ψ⁻¹(K) is compact.
 Hence IsEmbeddedSubmanifold r d M.
2. (Open pieces are submanifolds.) Let O ⊆ ℝ^P be open and w ∈ M ∩ O. By step 1 choose a chart (V, W, ψ) of M at w. As w ∈ W ∩ M = ψ(V), there is v ∈ V with ψ(v) = w. Put V' := V ∩ ψ⁻¹(O) and W' := W ∩ O. Then (V', W', ψ) is a chart of M ∩ O at w:
 - V' is open, since ψ is continuous on the open set V (C^r implies continuous) and O is open. W' is open and w ∈ W'.
 - ψ is C^r and injective on V' ⊆ V, and Dψ(z) is injective for z ∈ V'.
 - ψ(V') = ψ(V) ∩ O = (W ∩ M) ∩ O = W' ∩ (M ∩ O).
 - For compact K ⊆ W' we have ψ⁻¹(K) ⊆ ψ⁻¹(O), so V' ∩ ψ⁻¹(K) = V ∩ ψ⁻¹(K). This is compact because K ⊆ W.
 Moreover v ∈ V', because ψ(v) = w ∈ O. Every w ∈ M ∩ O has such a chart, so IsEmbeddedSubmanifold r d (M ∩ O).
3. (Tangent spaces.) Keep w, v, (V, W, ψ) and (V', W', ψ) from step 2, and use r ≥ 1.
 - chart_tangent_space for N := M and the chart (V, W, ψ) gives tangentSpace M (ψ v) = range Dψ(v).
 - chart_tangent_space for N := M ∩ O and the chart (V', W', ψ) gives tangentSpace (M ∩ O) (ψ v) = range Dψ(v).
 Since ψ(v) = w, tangentSpace (M ∩ O) w = tangentSpace M w. ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c, after `import GMT.Ch07.Submission`, in namespace GMT.Ch07 with the contract `open`s. It was compiled twice: in a standalone file, and spliced into a copy of GMT/Ch07/Submission.lean just before main_theorem. Each listed dependency was present under its exact frozen type, as an axiom standing in for the accepted or sibling declaration. `#print axioms` reports propext, Classical.choice and Quot.sound, plus exactly the declarations listed in depends_on (for reused children: their Submission names). It follows the numbered proof above.

```lean
theorem Submission.codim1_ovr_embedded_submanifold_local : ∀ (P r d : ℕ) (M : Set (Euclid P)), 1 ≤ r → (∀ y ∈ M, ∃ O : Set (Euclid P), IsOpen O ∧ y ∈ O ∧ IsEmbeddedSubmanifold r d (M ∩ O)) → IsEmbeddedSubmanifold r d M ∧ ∀ O : Set (Euclid P), IsOpen O → IsEmbeddedSubmanifold r d (M ∩ O) ∧ ∀ w ∈ M ∩ O, tangentSpace (M ∩ O) w = tangentSpace M w := by
  intro P r d M hr hloc
  -- part 1: local charts are charts of M
  have hM : IsEmbeddedSubmanifold r d M := by
    intro y hy
    obtain ⟨O, hO, hyO, hMO⟩ := hloc y hy
    obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, himg, hprop, hder⟩ := hMO y ⟨hy, hyO⟩
    refine ⟨V, W ∩ O, ψ, hV, hW.inter hO, ⟨hyW, hyO⟩, hψ, hinj, ?_, ?_, hder⟩
    · rw [himg]; ext z; simp only [mem_inter_iff]; tauto
    · intro K hK hKc; exact hprop K (hK.trans inter_subset_left) hKc
  -- part 2: restriction to open sets
  have hres : ∀ O : Set (Euclid P), IsOpen O → ∀ w ∈ M ∩ O, ∃ (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P) (v : Euclid d),
      IsOpen V ∧ IsOpen W ∧ w ∈ W ∧ ContDiffOn ℝ r ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ (M ∩ O) ∧
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧ (∀ z ∈ V, Injective (fderiv ℝ ψ z)) ∧
      v ∈ V ∧ ψ v = w ∧ tangentSpace M w = Set.range (fderiv ℝ ψ v) := by
    intro O hO w hw
    obtain ⟨V, W, ψ, hV, hW, hwW, hψ, hinj, himg, hprop, hder⟩ := hM w hw.1
    obtain ⟨v, hvV, hvw⟩ : w ∈ ψ '' V := by rw [himg]; exact ⟨hwW, hw.1⟩
    have hTM := Submission.chart_tangentSpace_eq_range_fderiv P d r M W V ψ v hr hV hW hψ hinj himg hprop hder hvV
    rw [hvw] at hTM
    refine ⟨V ∩ ψ ⁻¹' O, W ∩ O, ψ, v, hψ.continuousOn.isOpen_inter_preimage hV hO, hW.inter hO,
      ⟨hwW, hw.2⟩, hψ.mono inter_subset_left, hinj.mono inter_subset_left, ?_, ?_,
      fun z hz => hder z hz.1, ⟨hvV, by rw [mem_preimage, hvw]; exact hw.2⟩, hvw, hTM⟩
    · rw [image_inter_preimage, himg]; ext z; simp only [mem_inter_iff]; tauto
    · intro K hK hKc
      have h := hprop K (hK.trans inter_subset_left) hKc
      have heq : (V ∩ ψ ⁻¹' O) ∩ ψ ⁻¹' K = V ∩ ψ ⁻¹' K := by
        ext z; simp only [mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, (hK h3).2⟩, h3⟩
      rw [heq]; exact h
  refine ⟨hM, fun O hO => ⟨fun w hw => ?_, fun w hw => ?_⟩⟩
  · obtain ⟨V, W, ψ, v, hV, hW, hwW, hψ, hinj, himg, hprop, hder, -⟩ := hres O hO w hw
    exact ⟨V, W, ψ, hV, hW, hwW, hψ, hinj, himg, hprop, hder⟩
  · obtain ⟨V, W, ψ, v, hV, hW, hwW, hψ, hinj, himg, hprop, hder, hvV, hvw, hTM⟩ := hres O hO w hw
    have hTMO := Submission.chart_tangentSpace_eq_range_fderiv P d r (M ∩ O) W V ψ v hr hV hW hψ hinj himg hprop hder hvV
    rw [hvw] at hTMO
    rw [hTMO, hTM]
```

## Key steps

1. A chart (V, W, ψ) of M ∩ O at y gives the chart (V, W ∩ O, ψ) of M at y.
2. A chart (V, W, ψ) of M at w ∈ O restricts to the chart (V ∩ ψ⁻¹(O), W ∩ O, ψ) of M ∩ O at w.
3. chart_tangent_space computes both tangent spaces at w as range Dψ(ψ⁻¹(w)).

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
