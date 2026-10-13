# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.regular_point_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.regular_point_density-a1.locally_closed-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the supplied parent proof ("M ∩ closedBall y (2ρ₁) = ψ(V ∩ ψ⁻¹(closedBall y (2ρ₁))) is compact"), together with the measurability of M that the parent needs for the integrals ∫_M. Only continuity of ψ on V, ψ(V) = W ∩ M and the properness of the charts are used.
1. (Compact slices of a chart.) Let y ∈ M and let (V, W, ψ) be a chart at y given by IsEmbeddedSubmanifold r d M. Claim: for every compact K ⊆ W the set M ∩ K is compact. First, M ∩ K = ψ(V ∩ ψ⁻¹(K)). Indeed, if x ∈ M ∩ K then x ∈ W because K ⊆ W, so x ∈ W ∩ M = ψ(V); write x = ψ(v) with v ∈ V, and then v ∈ V ∩ ψ⁻¹(K). Conversely, for v ∈ V ∩ ψ⁻¹(K) we have ψ(v) ∈ ψ(V) = W ∩ M ⊆ M and ψ(v) ∈ K. Next, V ∩ ψ⁻¹(K) is compact by the properness clause of the chart, and ψ is continuous on V (a C^r map on V is continuous there, for every r ≥ 0), hence continuous on V ∩ ψ⁻¹(K). The continuous image of a compact set is compact, so M ∩ K is compact.
2. (Part (b).) W is open and y ∈ W, so there is r' > 0 with ball(y, r') ⊆ W. Put ε := r'/2 > 0. Then closedBall(y, ε) ⊆ ball(y, r') ⊆ W, and closedBall(y, ε) is compact because ℝ^P is a proper metric space. By step 1, M ∩ closedBall(y, ε) is compact.
3. (An open set containing M.) For each y ∈ M choose a chart (V_y, W_y, ψ_y) at y, and let O := ⋃_{y ∈ M} W_y. O is open, being a union of open sets, and M ⊆ O because y ∈ W_y.
4. (M = O ∩ closure(M).) The inclusion M ⊆ O ∩ closure(M) is clear from step 3. Conversely, let p ∈ O ∩ closure(M). Pick y ∈ M with p ∈ W_y and r' > 0 with ball(p, r') ⊆ W_y. The set C := M ∩ closedBall(p, r'/2) is compact by step 1 (closedBall(p, r'/2) is compact and contained in ball(p, r') ⊆ W_y), hence closed. Since ball(p, r'/2) is open, ball(p, r'/2) ∩ closure(M) ⊆ closure(ball(p, r'/2) ∩ M), and p belongs to the left-hand side. Hence p ∈ closure(ball(p, r'/2) ∩ M) ⊆ closure(C) = C ⊆ M.
5. (Part (a).) By step 4, M is the intersection of the open set O and the closed set closure(M). Open and closed sets are Borel, so M is measurable.

Lean reference proof (verified). The declaration below was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) inside a copy of GMT/Ch07/Submission.lean at this node's proof base (ee11750), placed after the contract definitions (namespace GMT.Ch07, contract `open`s, noncomputable section). `#print axioms` reports only propext, Classical.choice and Quot.sound. It follows the numbered proof above step by step.

```lean
theorem Submission.dimred_rpd_embedded_locally_closed : ∀ (P r d : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold r d M → MeasurableSet M ∧ ∀ y ∈ M, ∃ ε : ℝ, 0 < ε ∧ IsCompact (M ∩ closedBall y ε) := by
  intro P r d M hM
  have key : ∀ y ∈ M, ∃ W : Set (Euclid P), IsOpen W ∧ y ∈ W ∧
      ∀ K ⊆ W, IsCompact K → IsCompact (M ∩ K) := by
    intro y hy
    obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, himg, hprop, hder⟩ := hM y hy
    refine ⟨W, hW, hyW, fun K hKW hK => ?_⟩
    have hEq : M ∩ K = ψ '' (V ∩ ψ ⁻¹' K) := by
      ext x
      constructor
      · rintro ⟨hxM, hxK⟩
        have hx : x ∈ ψ '' V := by rw [himg]; exact ⟨hKW hxK, hxM⟩
        obtain ⟨v, hv, rfl⟩ := hx
        exact ⟨v, ⟨hv, hxK⟩, rfl⟩
      · rintro ⟨v, ⟨hv, hvK⟩, rfl⟩
        have hv' : ψ v ∈ W ∩ M := by rw [← himg]; exact ⟨v, hv, rfl⟩
        exact ⟨hv'.2, hvK⟩
    rw [hEq]
    exact (hprop K hKW hK).image_of_continuousOn (hψ.continuousOn.mono inter_subset_left)
  refine ⟨?_, ?_⟩
  · choose! Wf hWo hyW hcpt using key
    have hO : IsOpen (⋃ y ∈ M, Wf y) := isOpen_biUnion fun y hy => hWo y hy
    have hMeq : M = (⋃ y ∈ M, Wf y) ∩ closure M := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨mem_biUnion hx (hyW x hx), subset_closure hx⟩
      · rintro p ⟨hpO, hpcl⟩
        obtain ⟨y, hy, hpW⟩ := mem_iUnion₂.1 hpO
        obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 (hWo y hy) p hpW
        have hcb : closedBall p (r' / 2) ⊆ Wf y :=
          (closedBall_subset_ball (by linarith)).trans hball
        have hC := hcpt y hy (closedBall p (r' / 2)) hcb (isCompact_closedBall p (r' / 2))
        have h1 : p ∈ ball p (r' / 2) ∩ closure M := ⟨mem_ball_self (by linarith), hpcl⟩
        have h2 := isOpen_ball.inter_closure h1
        have hsub : ball p (r' / 2) ∩ M ⊆ M ∩ closedBall p (r' / 2) :=
          fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩
        have h3 : p ∈ closure (M ∩ closedBall p (r' / 2)) := closure_mono hsub h2
        rw [hC.isClosed.closure_eq] at h3
        exact h3.1
    rw [hMeq]
    exact hO.measurableSet.inter isClosed_closure.measurableSet
  · intro y hy
    obtain ⟨W, hW, hyW, hcpt⟩ := key y hy
    obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 hW y hyW
    exact ⟨r' / 2, by linarith,
      hcpt _ ((closedBall_subset_ball (by linarith)).trans hball) (isCompact_closedBall y _)⟩
```

## Key steps

1. Chart slices: for compact K ⊆ W, M ∩ K = ψ(V ∩ ψ⁻¹(K)) is compact by properness and continuity of ψ on V.
2. A closed ball around y inside the chart domain W meets M in a compact set.
3. With O the union of the chart domains, M = O ∩ closure(M), so M is Borel.

## Reference use

### local-project

Queries:
- `sha256sum GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical; manifest pins project b4d606d, mathlib 25730c7c)`
- `grep -n 'def massOn|def massAdmissibleOn|covectorEuclideanNorm|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'zeroRegion|def GeometricCurrentOn.support|VanishesOn' Chapter06/CurrentLocalEquality.lean; grep -n 'TestFormOn|structure GeometricCurrentOn' Chapter06/Currents.lean; grep -n 'IsTestForm|DifferentialForm|Covector' Chapter06/Forms.lean`
- `sed -n 1,200p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, euclideanHausdorffMeasure_zero, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image)`
- `grep -n 'hausdorffMeasure_image_le|hausdorffMeasure_zero_singleton' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'InnerRegularCompactLTTop|exists_isCompact_sdiff_lt' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean Mathlib/MeasureTheory/Measure/RegularityCompacts.lean; Lean: `μHE[n].InnerRegularCompactLTTop` fails under the contract imports but `(μHE[n].restrict A).InnerRegularCompactLTTop` succeeds for finite restrictions`
- `grep -n 'setIntegral_eq_zero_of_forall_eq_zero|setIntegral_union|setIntegral_ge_of_const_le_real|norm_setIntegral_le_of_norm_le_const' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -rn 'theorem ContDiffAt.hasStrictFDerivAt|theorem addHaar_ball_of_pos|theorem IsOpen.inter_closure|theorem IsCompact.image_of_continuousOn|theorem finrank_euclideanSpace_fin|theorem LinearMap.finrank_range_of_inj|theorem invFunOn_eq' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldTopology,AreaFormula,AreaNormalization}.lean (IsSimonLocalRepresentation, isEmbedding_chartMap, injective_area_formula_of_injective_derivative; none imported by the contract)`
- `python3 over dag.json: nodes whose lean_statement mentions IsEmbeddedSubmanifold, regularSet, covectorEuclideanNorm, IsUnitOrientationOf, μHE or massOn; accepted statuses; duplicate lean_names; grep -c dimred_rpd dag.json (0)`
- `git diff <proof_base> <candidate> -- GMT/Ch07/Submission.lean for 9c8432cb (dor_ims_unitOrientation_dual), 89e4c45c (dor_ims_smooth_unit_approx + dor_ims_sua_* helpers), 5e4b2158 (dsmc_chart_inverse_continuity): pure additions after RegularComponentsAreMinimizing`
- `nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v2.json (sibling precedent for reusing accepted declarations)`
- `lake env lean /tmp/rpd-check/Check.lean (types + assembly); /tmp/rpd-check/{C1,C4,C7}.lean; /tmp/rpd-final/Final.lean (stubs for reused); /tmp/rpd-final/Full.lean and /tmp/rpd-final/SubmissionCopy.lean (accepted reused proofs spliced in; #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v2.json`
- `/tmp/rpd-final/Final.lean`
- `/tmp/rpd-final/SubmissionCopy.lean`

Pins match: the snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (sha256 e4148e7f…), and the manifest pins project b4d606d and mathlib 25730c7c.

Available under the contract imports:
- μHE[d] = c_d·μH[d] with one constant on every metric space, and μHE[n] = volume on Euclid n;
- LipschitzOnWith.hausdorffMeasure_image_le;
- ContDiffAt.hasStrictFDerivAt;
- Measure.addHaar_ball_of_pos;
- inner regularity (InnerRegularCompactLTTop) for finite restrictions μHE[n]⌞A, though not for μHE[n] itself.

Not available: SimonGMT's chart-embedding and area-formula modules (Chapter02) are not imported by the contract. No library lemma gives the mass of a local m₀[[M]] current or the density of a C¹ submanifold.

Reused building blocks: Submission.dor_ims_unitOrientation_dual, Submission.dor_ims_smooth_unit_approx and Submission.dsmc_chart_inverse_continuity are accepted DAG nodes with candidate commits. Their frozen types are reused byte-for-byte, following the sibling precedent one_dim_cones-a1 v2. No new name collides: there are 0 hits for dimred_rpd_.

Lean evidence: all child types and the parent assembly elaborate. With the accepted reused proofs spliced in, the selected theorem compiles inside a copy of Submission.lean with axioms propext, Classical.choice and Quot.sound only.
