# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.lipschitz_approx-a1.tangent_uniqueness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 7b of the parent proof ("derivatives within M at x are unique on T_x, which is spanned by velocities of C¹ curves in M through x"), also used in its step 8. The statement holds for an arbitrary set M ⊆ ℝ^P; no submanifold hypothesis is needed.

1. (A derivative within M.) By hypothesis f has derivative f' within M at x, so f is differentiable within M at x. Hence f also has derivative L := fderivWithin ℝ f M x within M at x (Mathlib DifferentiableWithinAt.hasFDerivWithinAt; this holds also when x is isolated in M, where every linear map is a derivative within M).
2. (Uniqueness on the tangent cone.) Two derivatives of f within M at x agree on the tangent cone tangentConeAt ℝ M x (Mathlib HasFDerivWithinAt.unique_on). So L u = f' u for every u in the tangent cone.
3. (Curve velocities lie in the tangent cone.) Let w ∈ tangentSpace M x: there is γ : ℝ → ℝ^P, C¹ on (−1,1), with γ((−1,1)) ⊆ M, γ(0) = x and γ'(0) = w. Put t_n := 1/(n+2) ∈ (0, 1/2] (n ∈ ℕ), c_n := n + 2 and d_n := γ(t_n) − x. Then (i) x + d_n = γ(t_n) ∈ M because t_n ∈ (−1,1); (ii) d_n → 0 because γ is continuous at 0 (it is differentiable there) and t_n → 0; (iii) c_n·d_n = t_n⁻¹(γ(0 + t_n) − γ(0)) → w, because t_n → 0 with t_n ≠ 0 and the difference quotients of γ at 0 converge to γ'(0) = w (hasDerivAt_iff_tendsto_slope_zero). By mem_tangentConeAt_of_seq, w ∈ tangentConeAt ℝ M x.
4. (Passage to the span.) By steps 2 and 3, L and f' agree on tangentSpace M x. The set {u : L u = f' u} is the kernel of the linear map L − f', a linear subspace of ℝ^P; it contains tangentSpace M x and therefore its span. Hence fderivWithin ℝ f M x v = L v = f' v for every v ∈ span(tangentSpace M x). ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below of `theorem Submission.codim1_hcp_lsa_fderivWithin_eq_on_tangent_span : <exactly the frozen lean_statement> := by`, after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the contract's opens, compiled with Lean v4.35.0-rc3 / Mathlib 25730c7c; #print axioms: propext, Classical.choice, Quot.sound.
```lean
  intro P M f f' x v hf hv
  -- the chosen derivative within `M` is a derivative within `M`
  have hf₁ : HasFDerivWithinAt f (fderivWithin ℝ f M x) M x :=
    hf.differentiableWithinAt.hasFDerivWithinAt
  -- every velocity of a curve in `M` through `x` lies in the tangent cone of `M` at `x`
  have hcone : tangentSpace M x ⊆ tangentConeAt ℝ M x := by
    rintro w ⟨γ, -, hγM, hγ0, hγd⟩
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) + 1)) atTop (𝓝 0) :=
          this.comp (tendsto_add_atTop_nat 1)
        refine h2.congr fun n => ?_
        push_cast; ring_nf
      · simp only [mem_compl_iff, mem_singleton_iff]; positivity
    have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 hγd).comp ht
    refine mem_tangentConeAt_of_seq atTop (fun n : ℕ => (n : ℝ) + 2)
      (fun n => γ ((1 : ℝ) / ((n : ℝ) + 2)) - x) ?_ ?_ ?_
    · have hc : Tendsto (fun n : ℕ => γ ((1 : ℝ) / ((n : ℝ) + 2))) atTop (𝓝 (γ 0)) :=
        (hγd.continuousAt.tendsto).comp (tendsto_nhdsWithin_iff.1 ht).1
      rw [hγ0] at hc
      simpa using hc.sub_const x
    · refine Eventually.of_forall fun n => ?_
      have hmem : (1 : ℝ) / ((n : ℝ) + 2) ∈ Ioo (-1 : ℝ) 1 := by
        constructor
        · have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
          linarith
        · rw [div_lt_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
      simpa using hγM hmem
    · refine hslope.congr fun n => ?_
      simp only [Function.comp_apply, hγ0, zero_add]
      rw [one_div, inv_inv]
  -- two derivatives within `M` agree on the tangent cone, hence on the span of `tangentSpace M x`
  have heq : EqOn (fderivWithin ℝ f M x) f' (tangentConeAt ℝ M x) := hf₁.unique_on hf
  let K : Submodule ℝ (Euclid P) := LinearMap.ker ((fderivWithin ℝ f M x - f' : Euclid P →L[ℝ] ℝ) : Euclid P →ₗ[ℝ] ℝ)
  have hK : tangentSpace M x ⊆ K := by
    intro w hw
    change fderivWithin ℝ f M x w - f' w = 0
    exact sub_eq_zero.2 (heq (hcone hw))
  have := (Submodule.span_le.2 hK) hv
  simpa [K, sub_eq_zero] using this

```

Integration check: this proof was also compiled together with the proofs of all eight new sibling children and the assembly of the parent theorem in a single file (only the four reused accepted declarations taken as axioms); the file compiled without errors or `sorry`.

## Key steps

1. fderivWithin ℝ f M x is itself a derivative of f within M at x.
2. Any two derivatives within M agree on tangentConeAt ℝ M x (HasFDerivWithinAt.unique_on).
3. γ'(0) = lim (n+2)(γ(1/(n+2)) − x) lies in the tangent cone.
4. The agreement set is the kernel of a linear map, so it contains the span of tangentSpace M x.

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
