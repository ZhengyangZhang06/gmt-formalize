# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.rademacher-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. The Rademacher part of steps 7b and 8 of the parent proof (Simon Ch. 2, 4.5–4.9: Rademacher's theorem on M through local coordinates): in a graph chart G on which ζ is Lipschitz, ζ∘G is differentiable outside an L^m-null set N (Mathlib LipschitzOnWith.ae_differentiableWithinAt_of_mem), the exceptional set G(N) is H^m-null (Lipschitz images), and countably many charts cover M (second countability). Sibling children used: graph_chart, lipschitz_transfer, locally_closed. H^m = μHE[m], L^m = volume on ℝ^m.

1. (M is Borel.) By child locally_closed (part (a)), M is a measurable set.
2. (Local claim.) For every p ∈ M there are an open set O ∋ p and a set E ⊆ ℝ^P with H^m(E) = 0 such that ζ is differentiable within M at every x ∈ (M ∩ O) \ E. Proof:
 (a) Child graph_chart at p gives pr, G, r, W, Λ (W open, p ∈ W, G(0) = p, G C¹ and Λ-Lipschitz on B_r(0), M ∩ W = G(B_r(0)), pr(G(a) − p) = a on B_r(0)).
 (b) ζ is locally Lipschitz on M: there are K ≥ 0 and t ∈ 𝓝[M] p with ζ K-Lipschitz on t; choose an open U ∋ p with M ∩ U ⊆ t.
 (c) G is continuous at 0 with G(0) = p ∈ U, so there is r₁ ∈ (0, r] with G(B_{r₁}(0)) ⊆ U. Let O := W ∩ {z : pr(z − p) ∈ B_{r₁}(0)}; O is open and p ∈ O.
 (d) Every x ∈ M ∩ O is G(a) with a := pr(x − p) ∈ B_{r₁}(0): indeed x ∈ M ∩ W = G(B_r(0)), x = G(b), and b = pr(G(b) − p) = pr(x − p) = a ∈ B_{r₁}(0).
 (e) For a ∈ B_{r₁}(0), G(a) ∈ M (as G(B_r(0)) = M ∩ W) and G(a) ∈ U, so G(a) ∈ M ∩ U ⊆ t. Hence g := ζ∘G is KΛ-Lipschitz on B_{r₁}(0).
 (f) By Rademacher's theorem for functions Lipschitz on a set, for L^m-a.e. a ∈ B_{r₁}(0), g is differentiable within B_{r₁}(0) at a, hence differentiable at a (the ball is open). So N := {a ∈ B_{r₁}(0) : g not differentiable at a} satisfies L^m(N) = 0.
 (g) Put E := G(N). By child lipschitz_transfer, part (a), applied to G (Λ-Lipschitz on B_{r₁}(0) ⊆ B_r(0)) and N ⊆ B_{r₁}(0): H^m(E) ≤ Λ^m·L^m(N) = 0.
 (h) Let x ∈ (M ∩ O) \ E and a := pr(x − p). By (d), a ∈ B_{r₁}(0) and G(a) = x; as x ∉ G(N), a ∉ N, so g is differentiable at a. Then f(z) := g(pr(z − p)) is differentiable at x (chain rule with the affine map z ↦ pr(z − p)). For y ∈ M ∩ O, (d) gives f(y) = ζ(G(pr(y − p))) = ζ(y); M ∩ O ∈ 𝓝[M] x since O is open; and f(x) = ζ(x). Hence ζ is differentiable within M at x (DifferentiableWithinAt.congr_of_eventuallyEq).
3. (Countable cover.) Choose O_p, E_p as in step 2 for every p ∈ M. Since ℝ^P is second countable there is a countable T ⊆ M with ⋃_{p∈T} O_p = ⋃_{p∈M} O_p (TopologicalSpace.isOpen_biUnion_countable); the latter contains M because p ∈ O_p. E := ⋃_{p∈T} E_p is a countable union of H^m-null sets, hence H^m(E) = 0.
4. (Conclusion.) Let x ∈ M be a point at which ζ is not differentiable within M. Choose p ∈ T with x ∈ O_p; by step 2(h) applied to p, x ∈ E_p ⊆ E. So {x ∈ M : ζ not differentiable within M at x} ⊆ E is H^m-null. Since M is measurable (step 1), this is exactly the statement ∀ᵐ x ∂(H^m⌞M), DifferentiableWithinAt ℝ ζ M x (ae_restrict_iff', ae_iff). ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below of `theorem Submission.codim1_hcp_lsa_rademacher_on_submanifold : <exactly the frozen lean_statement> := by`, after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the contract's opens and with the siblings Submission.dimred_rpd_embedded_locally_closed, Submission.codim1_hcp_lsa_c1_graph_chart and Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le present with their frozen types, compiled with Lean v4.35.0-rc3 / Mathlib 25730c7c; #print axioms: propext, Classical.choice, Quot.sound and those three siblings.
```lean
  intro P m M ζ hM hζ
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  -- local statement: near each `p ∈ M`, `ζ` is differentiable within `M` off an `Hᵐ`-null set
  have hloc : ∀ p ∈ M, ∃ O : Set (Euclid P), IsOpen O ∧ p ∈ O ∧ ∃ E : Set (Euclid P),
      μHE[m] E = 0 ∧ ∀ x ∈ M ∩ O, x ∉ E → DifferentiableWithinAt ℝ ζ M x := by
    intro p hp
    obtain ⟨pr, G, r, W, Λ, hr, hWo, hpW, hpr, hG0, hGc, hGL, hMW, hleft, hderiv, htan⟩ :=
      Submission.codim1_hcp_lsa_c1_graph_chart P m M p hM hp
    obtain ⟨K, t, ht, hKt⟩ := hζ hp
    obtain ⟨U, hUo, hpU, hUt⟩ : ∃ U : Set (Euclid P), IsOpen U ∧ p ∈ U ∧ M ∩ U ⊆ t := by
      rw [mem_nhdsWithin] at ht
      obtain ⟨U, hUo, hpU, hUt⟩ := ht
      exact ⟨U, hUo, hpU, fun x hx => hUt ⟨hx.2, hx.1⟩⟩
    -- shrink the chart so that its image lies in `U`
    obtain ⟨r₁, hr₁, hr₁r, hGU⟩ : ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ r ∧ G '' ball 0 r₁ ⊆ U := by
      have hGcont : ContinuousAt G 0 :=
        hGc.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
      have hpre : G ⁻¹' U ∈ 𝓝 (0 : Euclid m) :=
        hGcont.preimage_mem_nhds (hUo.mem_nhds (by rw [hG0]; exact hpU))
      obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hpre
      refine ⟨min ε r, lt_min hε hr, min_le_right _ _, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      exact hεU (ball_subset_ball (min_le_left _ _) ha)
    have hball : ball (0 : Euclid m) r₁ ⊆ ball 0 r := ball_subset_ball hr₁r
    let O : Set (Euclid P) := W ∩ (fun z => pr (z - p)) ⁻¹' ball 0 r₁
    have hOo : IsOpen O := hWo.inter (isOpen_ball.preimage (by fun_prop))
    have hpO : p ∈ O := ⟨hpW, by simp [hr₁]⟩
    -- every point of `M ∩ O` is `G a` with `a = pr (x - p) ∈ ball 0 r₁`
    have hMO : ∀ x ∈ M ∩ O, pr (x - p) ∈ ball (0 : Euclid m) r₁ ∧ G (pr (x - p)) = x := by
      intro x hx
      have hxW : x ∈ M ∩ W := ⟨hx.1, hx.2.1⟩
      rw [hMW] at hxW
      obtain ⟨a, ha, rfl⟩ := hxW
      rw [hleft a ha]
      refine ⟨?_, rfl⟩
      have h2 : pr (G a - p) ∈ ball (0 : Euclid m) r₁ := hx.2.2
      rwa [hleft a ha] at h2
    have hGM : ∀ a ∈ ball (0 : Euclid m) r, G a ∈ M := fun a ha =>
      ((hMW.symm ▸ mem_image_of_mem G ha : G a ∈ M ∩ W)).1
    -- `ζ ∘ G` is Lipschitz on `ball 0 r₁`
    have hgL : LipschitzOnWith (K * Λ) (ζ ∘ G) (ball 0 r₁) :=
      hKt.comp (hGL.mono hball) fun a ha => hUt ⟨hGM a (hball ha), hGU (mem_image_of_mem G ha)⟩
    -- Rademacher on the ball
    let N : Set (Euclid m) := {a | a ∈ ball (0 : Euclid m) r₁ ∧ ¬ DifferentiableAt ℝ (ζ ∘ G) a}
    have hN : volume N = 0 := by
      have hrad := hgL.ae_differentiableWithinAt_of_mem (μ := volume)
      rw [ae_iff] at hrad
      refine measure_mono_null (fun a ha => ?_) hrad
      simp only [mem_setOf_eq, not_imp]
      exact ⟨ha.1, fun hd => ha.2 (hd.differentiableAt (isOpen_ball.mem_nhds ha.1))⟩
    refine ⟨O, hOo, hpO, G '' N, ?_, ?_⟩
    · have h := (Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le m P G (ball 0 r₁) Λ
        (hGL.mono hball)).1 N (fun a ha => ha.1)
      rw [hN, mul_zero] at h
      exact le_antisymm h zero_le
    · intro x hx hxE
      obtain ⟨ha, hGa⟩ := hMO x hx
      have hdiffa : DifferentiableAt ℝ (ζ ∘ G) (pr (x - p)) := by
        by_contra hnd
        exact hxE ⟨pr (x - p), ⟨ha, hnd⟩, hGa⟩
      have hpr' : DifferentiableAt ℝ (fun z : Euclid P => pr (z - p)) x := by fun_prop
      have hf : DifferentiableAt ℝ ((ζ ∘ G) ∘ fun z : Euclid P => pr (z - p)) x :=
        hdiffa.comp x hpr'
      refine hf.differentiableWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [inter_mem_nhdsWithin M (hOo.mem_nhds hx.2)] with y hy
        simp only [Function.comp_apply, (hMO y ⟨hy.1, hy.2⟩).2]
      · simp only [Function.comp_apply, hGa]
  -- countably many such neighbourhoods cover `M`
  choose! O hOo hpO E hE hdiff using hloc
  obtain ⟨T, hTM, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable M O hOo
  have hnull : μHE[m] (⋃ p ∈ T, E p) = 0 :=
    (measure_biUnion_null_iff hTc).2 fun p hp => hE p (hTM hp)
  rw [ae_restrict_iff' hMmeas, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [mem_setOf_eq, not_imp] at hx
  obtain ⟨hxM, hxnd⟩ := hx
  have hxU : x ∈ ⋃ p ∈ M, O p := mem_iUnion₂.2 ⟨x, hxM, hpO x hxM⟩
  rw [← hTU] at hxU
  obtain ⟨p, hpT, hxO⟩ := mem_iUnion₂.1 hxU
  refine mem_iUnion₂.2 ⟨p, hpT, ?_⟩
  by_contra hxE
  exact hxnd (hdiff p (hTM hpT) x ⟨hxM, hxO⟩ hxE)
```

Integration check: this proof was also compiled together with the proofs of all eight new sibling children and the assembly of the parent theorem in a single file (only the four reused accepted declarations taken as axioms); the file compiled without errors or `sorry`.

## Key steps

1. Near p ∈ M, shrink a graph chart so that ζ is Lipschitz on M ∩ O and M ∩ O = G(B_{r₁}(0)).
2. ζ∘G is Lipschitz on the ball, so it is differentiable off an L^m-null set N (Rademacher). G(N) is H^m-null by lipschitz_transfer.
3. Off G(N), ζ agrees on M near x with the ambient differentiable function g(pr(· − p)).
4. Countably many such O cover M (second countability).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (Euclid, IsEmbeddedSubmanifold, tangentSpace, μHE usage)`
- `python3 scans of dag.json: selected node (depth 5, max_depth 6), parent hypercone_plane and its decomposition-v1.json, accepted nodes whose statements mention Lipschitz/mollif/convol/graph chart/starProjection/tangentSpace, lean_name collision scan for codim1_hcp_lsa_*`
- `runtime.py: _decompose (max_depth), _existing_lean_name_problem (reuse of accepted declarations by identical name and type)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 93f7ea7a3650 (codim1_rdo_gc_local_inverse_c2, dsmc_chart_inverse_continuity), d25d2377 (codim1_zsl_pc_mollify_indicator_l1), and the handoffs of codim1_zsl_gc_local_inverse and dsmc_chart_inverse_continuity`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: euclideanHausdorffMeasure, ae_differentiableWithinAt_of_mem, LipschitzWith.ae_differentiableAt, measurable_fderiv, tangentConeAt, HasFDerivWithinAt.unique_on, mem_tangentConeAt_of_seq, hasFDerivAt_convolution_left, contDiff_convolution_left, ae_convolution_tendsto_right_of_locallyIntegrable, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact, LocallyLipschitzOn.mul, exists_isSubordinate, exists_contDiff_support_eq_eq_one_iff, sq_sum_le_card_mul_sum_sq, measurePreserving_sub_left`
- `lean #check probes in the GMT.Ch07.Submission import closure (Imp*.lean, Inst5.lean): SmoothPartitionOfUnity.exists_isSubordinate, ContDiffBump API, ContDiffBump.normed (missing), VitaliFamily.ae_tendsto_average_norm_sub, Besicovitch.tendsto_filterAt, tendsto_integral_smul_of_tendsto_average_norm_sub, aestronglyMeasurable_iUnion_iff, Submodule.eq_starProjection_of_mem_of_inner_eq_zero, NormedRing.inverse_continuousAt, instances HasContDiffBump/HasBesicovitchCovering (Euclid m)`
- `lean -DautoImplicit=false /tmp/lsa-split/check/{TypesAll,Assembly,N1,N2,N3,N4,N5,N6,N7,N8,Integration}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `git for-each-ref | xargs git grep -l codim1_hcp_lsa -- 'GMT/*.lean' (no match); grep codim1_hcp_lsa dag.json (0); grep -rn codim1_hcp_lsa simongmt (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e9797ac1a5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2511ff6312/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/TangentCone/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/tmp/lsa-split/check/TypesAll.lean`
- `/tmp/lsa-split/check/Assembly.lean`
- `/tmp/lsa-split/check/Integration.lean`

Pins match: manifest project b4d606db and Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib, and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). The node has depth 5 with max_depth 6, so the children are leaves. Reuse: four accepted declarations (chart_tangentSpace_eq_range_fderiv, dimred_rpd_embedded_locally_closed, codim1_zsl_gc_local_inverse, dsmc_chart_inverse_continuity) are taken with byte-identical frozen types. The C² graph-chart and tangent-projection lemmas (codim1_rdo_gc_graph_over_tangent, submanifold_tangentProjection_c1_extension, dor_lmb_ret_tangent_projection) do not apply to C¹ M. No C¹ graph chart, Rademacher-on-M, tangent-projection continuity or L²-gradient mollification lemma exists in the DAG, SimonGMT or the snapshot, and the 8 codim1_hcp_lsa_ names are unused everywhere. Mathlib in the Submission import closure provides Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem), measurable_fderiv, HasFDerivWithinAt.unique_on with mem_tangentConeAt_of_seq, LipschitzOnWith.hausdorffMeasure_image_le with EuclideanSpace.euclideanHausdorffMeasure_eq_volume, convolution smoothness, ContDiffBump, Besicovitch Lebesgue differentiation, SmoothPartitionOfUnity and exists_contDiff_support_eq_eq_one_iff. It lacks ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and sq_sum_le_card_mul_sum_sq; the mollify proof rebuilds the first two by hand, and the assembly uses Finset.sum_mul_sq_le_sq_mul_sq. Lean: all 12 child types elaborate. The selected type is kernel-checked from the child types as axioms. Every new child is proved from exactly its declared siblings. The integrated file (8 proofs plus assembly, only the 4 reused declarations as axioms) compiles without errors or sorry.
