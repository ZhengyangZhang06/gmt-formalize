# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_chart-a1.graph_cylinder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 9–10 of the supplied proof of the selected node graph_chart (choice of the radii δ₁, δ₂ and the identity N ∩ Z = Γ(B_{δ₁})), using only the graph properties that the parent's steps 7–8 provide (here hypotheses).
1. (Pythagoras.) For a ∈ ℝ^d and b ∈ ℝ^k, ‖ιa + ι'b‖² = ‖ιa‖² + 2⟨ιa, ι'b⟩ + ‖ι'b‖² = ‖a‖² + ‖b‖² (norm_add_sq_real, orthogonality, LinearIsometry.norm_map). In particular, if ιa + ι'b = 0 then ‖a‖² + ‖b‖² = 0, so a = 0.
2. (Radii.) Put δ₂ := s/2 > 0. Since u is continuous at 0 and u(0) = 0, there is η > 0 with ‖u(v)‖ < s/2 whenever ‖v‖ < η (Metric.continuousAt_iff). Since O is open and 0 ∈ O, there is ρ > 0 with ball(0, ρ) ⊆ O (Metric.isOpen_iff). Put δ₁ := min(min(η, ρ), s/2) > 0. Then ball(0, δ₁) ⊆ ball(0, ρ) ⊆ O, and every v ∈ ball(0, δ₁) has ‖v‖ < η, hence ‖u(v)‖ < δ₂, i.e. u(v) ∈ ball(0, δ₂).
3. (Γ(ball(0, δ₁)) ⊆ N ∩ Z, where Z := {x + ιv + ι'w : |v| < δ₁, |w| < δ₂}.) Let v ∈ ball(0, δ₁). Then v ∈ O, so Γ(v) ∈ N; and Γ(v) = x + ιv + ι'w with w := u(v) ∈ ball(0, δ₂) by step 2, so Γ(v) ∈ Z.
4. (N ∩ Z ⊆ Γ(ball(0, δ₁)).) Let y ∈ N ∩ Z, say y = x + ιv' + ι'w' with ‖v'‖ < δ₁ ≤ s/2 and ‖w'‖ < δ₂ = s/2. Then |y − x| = ‖ιv' + ι'w'‖ ≤ ‖ιv'‖ + ‖ι'w'‖ = ‖v'‖ + ‖w'‖ < s (triangle inequality, isometries). By hypothesis y = Γ(v) = x + ιv + ι'u(v) for some v ∈ O. Cancelling x gives ιv' + ι'w' = ιv + ι'u(v), i.e. ι(v' − v) + ι'(w' − u(v)) = 0, so v' − v = 0 by step 1. Hence y = Γ(v') with v' ∈ ball(0, δ₁).
5. Steps 2–4 give δ₁ > 0 and δ₂ > 0 with ball(0, δ₁) ⊆ O, u(ball(0, δ₁)) ⊆ ball(0, δ₂) and N ∩ Z = Γ(ball(0, δ₁)). ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below, for `theorem Submission.codim1_zsl_gc_graph_cylinder : <exactly the frozen lean_statement> := by`, compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, with the contract's `open`s inside `namespace GMT.Ch07`, using the default maxHeartbeats (it also compiles under maxHeartbeats 60000), no helper declaration and no set_option. It needs no other declaration: it was compiled on its own (#print axioms: propext, Classical.choice, Quot.sound) and again inside an integration file containing all five new children, the actual proofs of the five reused declarations (taken from their candidate commits) and the assembly of the selected theorem, whose #print axioms gave propext, Classical.choice, Quot.sound.
```lean
  intro d k N x ι ι' O u s horth hO h0O hu hu0 hs hN hfib
  -- `ι a + ι' b = 0` forces `a = 0` (Pythagoras)
  have hinj : ∀ a b, ι a + ι' b = 0 → a = 0 := by
    intro a b h
    have h1 := norm_add_sq_real (ι a) (ι' b)
    rw [h, horth, ι.norm_map, ι'.norm_map, norm_zero] at h1
    have h2 : ‖a‖ = 0 := by nlinarith [norm_nonneg a, sq_nonneg ‖b‖]
    exact norm_eq_zero.mp h2
  obtain ⟨η, hη, hηu⟩ := Metric.continuousAt_iff.mp hu (s / 2) (half_pos hs)
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.mp hO 0 h0O
  have hδ₁ : 0 < min (min η ρ) (s / 2) := lt_min (lt_min hη hρ) (half_pos hs)
  have hballO : ball (0 : Euclid d) (min (min η ρ) (s / 2)) ⊆ O :=
    (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))).trans hρO
  have hball2 : ∀ v ∈ ball (0 : Euclid d) (min (min η ρ) (s / 2)),
      u v ∈ ball (0 : Euclid k) (s / 2) := by
    intro v hv
    have hv' : dist v 0 < η :=
      lt_of_lt_of_le (mem_ball.mp hv) ((min_le_left _ _).trans (min_le_left _ _))
    have h := hηu hv'
    rw [hu0] at h
    exact mem_ball.mpr h
  refine ⟨min (min η ρ) (s / 2), s / 2, hδ₁, half_pos hs, hballO, hball2, ?_⟩
  ext y
  constructor
  · rintro ⟨hyN, v', hv', w', hw', rfl⟩
    have hv's : ‖v'‖ < s / 2 :=
      lt_of_lt_of_le (mem_ball_zero_iff.mp hv') (min_le_right _ _)
    have hw's : ‖w'‖ < s / 2 := mem_ball_zero_iff.mp hw'
    have hdist : dist (x + ι v' + ι' w') x < s := by
      rw [dist_eq_norm, add_assoc, add_sub_cancel_left]
      calc ‖ι v' + ι' w'‖ ≤ ‖ι v'‖ + ‖ι' w'‖ := norm_add_le _ _
        _ = ‖v'‖ + ‖w'‖ := by rw [ι.norm_map, ι'.norm_map]
        _ < s / 2 + s / 2 := add_lt_add hv's hw's
        _ = s := add_halves s
    obtain ⟨v, -, hv⟩ := hfib _ hyN hdist
    have hv2 : ι v' + ι' w' = ι v + ι' (u v) := by
      rw [add_assoc, add_assoc] at hv
      exact add_left_cancel hv
    have h3 : ι (v' - v) + ι' (w' - u v) = 0 := by
      rw [map_sub, map_sub, sub_add_sub_comm, hv2, sub_self]
    have hvv : v' = v := sub_eq_zero.mp (hinj _ _ h3)
    exact ⟨v, hvv ▸ hv', hv.symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hN v (hballO hv), v, hv, u v, hball2 v hv, rfl⟩
```

## Key steps

1. ‖ιa + ι'b‖² = ‖a‖² + ‖b‖², so ιa + ι'b = 0 forces a = 0.
2. δ₂ := s/2 and δ₁ := min(η, ρ, s/2), where ‖u‖ < δ₂ on ball(0, η) and ball(0, ρ) ⊆ O.
3. ⊇: Γ(v) ∈ N and u(v) ∈ ball(0, δ₂) for v ∈ ball(0, δ₁).
4. ⊆: a point x + ιv' + ι'w' of N ∩ Z is within s of x, hence equals Γ(v) for some v, and comparing ι-components gives v = v'.

## Reference use

### local-project

Queries:
- `cat nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-3803907b64/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sed -n 1,457p GMT/Ch07/Contract.lean (Euclid, MultiVector, IsUnitOrientationOf, IsEmbeddedSubmanifold, tangentSpace, IsOrientation); sed -n 1,60p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean (Covector = E [⋀^Fin n]→L[ℝ] ℝ)`
- `grep -n 'def check_source_delta' -A40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py; sed -n 3159,3200p runtime.py (_overlay_accepted_children merges candidate histories)`
- `python3 scan of dag.json: accepted nodes whose lean_statement mentions tangentSpace, IsUnitOrientationOf, Orthonormal or →ₗᵢ; the region_density_one-a1.graph_chart-a1 branch (codim1_rdo_gc_*, all decomposing, not reusable)`
- `python3: exact lean_statement of rsdic_unitOrientation_eq_or_eq_neg, dgcr_graph_orientation_jacobian, dsmc_chart_range_subset_tangentSpace, dsmc_chart_inverse_continuity, dorag_lip_orthonormal_coordinates and codim1_zsl_oriented_graph_chart from dag.json; comparison with the handoff and with decomposition-v2.json of the parent (identical)`
- `git show <candidate>:GMT/Ch07/Submission.lean for fe95347baaed, 62aa1f119348, 8f402cb9186d, 5e4b21584624, dd8fcf8bcea7; pairwise git merge-base --is-ancestor (none) and declaration sets (disjoint)`
- `grep -rl codim1_zsl_gc dag.json nodes/ GMT .lake/packages/simongmt/Poincare local-references/123e8435b4a2469b/project (no match); for r in $(git for-each-ref --format='%(objectname)' | sort -u): git grep -q -e codim1_zsl_gc $r -- 'GMT/*.lean' (1523 refs, 0 hits; positive control dgcr_graph_orientation_jacobian: 8 hits)`
- `rg -n in local-references/123e8435b4a2469b/mathlib/Mathlib: OpenPartialHomeomorph.contDiffAt_symm, toOpenPartialHomeomorph, ContinuousLinearEquiv.isOpen, ofInjectiveEndo, restrOpen, ContinuousAlternatingMap.apply, reflection_orthogonalComplement_singleton_eq_neg, reflection_mem_subspace_eq_self, reflection_reflection, Orthonormal.comp_linearIsometry, EuclideanSpace.orthonormal_single, LinearIsometry.adjoint_comp_self, finrank_span_eq_card, eq_of_le_of_finrank_eq, IsPreconnected.intermediate_value, ContinuousOn.clm_apply, map_update_smul, ContDiffOn.continuousOn_fderiv_of_isOpen, starProjection_eq_self_iff, norm_add_sq_real, mem_orthogonal_singleton_iff_inner_right, adjoint_inner_left`
- `lake env lean -DautoImplicit=false /tmp/gc-split/Types.lean (10 child types + selected type, exit 0)`
- `lake env lean -DautoImplicit=false /tmp/gc-split/Assembly.lean (children as axioms; #print axioms)`
- `lake env lean -DautoImplicit=false /tmp/gc-split/{oriented_frame,local_inverse,local_graph,graph_cylinder,orientation_along_graph}/Proof.lean; /tmp/gc-split/Combined.lean and Combined_hb60000.lean (all exit 0)`
- `lake env lean -DautoImplicit=false /tmp/gc-split/Integration.lean (real accepted proofs of the 5 reused declarations + 5 new proofs + assembly; exit 0; #print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/IntermediateValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-3803907b64/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-3803907b64/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-v2.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/gc-split/Types.lean`
- `/tmp/gc-split/Assembly.lean`
- `/tmp/gc-split/Combined_hb60000.lean`
- `/tmp/gc-split/Integration.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, which equal workspace HEAD and .lake/packages/mathlib. The workspace Contract.lean and Submission.lean are byte-identical, and the frozen selected type in dag.json equals the handoff's.
Reuse. Five accepted declarations cover parts of the supplied proof, and each is reused with its byte-identical dag.json type:
- rsdic_unitOrientation_eq_or_eq_neg (fe95347baaed)
- dgcr_graph_orientation_jacobian (62aa1f119348)
- dsmc_chart_range_subset_tangentSpace (8f402cb9186d), parent steps 5 and 11
- dsmc_chart_inverse_continuity (5e4b21584624), parent step 8
- dorag_lip_orthonormal_coordinates (dd8fcf8bcea7), parent step 2
The similar codim1_rdo_gc_* nodes of the region_density_one graph_chart branch are only decomposing and have other types, so none is reused.
Names. The 5 new names codim1_zsl_gc_* have no match in dag.json, nodes/, GMT/, SimonGMT, the snapshot project, or GMT/*.lean at any of 1523 ref tips.
Mathlib. Every Mathlib lemma cited by the children exists in the snapshot, for example:
- OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881)
- HasStrictFDerivAt.toOpenPartialHomeomorph (InverseFunctionTheorem/FDeriv.lean:117)
- ContinuousLinearEquiv.isOpen (BoundedLinearMaps.lean:543)
- OpenPartialHomeomorph.restrOpen (OpenPartialHomeomorph/IsImage.lean:216)
- ContinuousAlternatingMap.apply (Alternating/Topology.lean:294)
- the reflection lemmas (Projection/Reflection.lean:81, 117, 150)
- LinearIsometry.adjoint_comp_self (Adjoint.lean:1066)
- IsPreconnected.intermediate_value (Order/IntermediateValue.lean:125)
Lean.
- All 10 child types and the selected type elaborate.
- The selected type follows from the 4 direct children with only standard axioms.
- Each new child has a compiled single-theorem proof under default heartbeats (also under 60000).
- The final integration with the real accepted proofs compiles; the selected theorem's axioms are propext, Classical.choice and Quot.sound.
