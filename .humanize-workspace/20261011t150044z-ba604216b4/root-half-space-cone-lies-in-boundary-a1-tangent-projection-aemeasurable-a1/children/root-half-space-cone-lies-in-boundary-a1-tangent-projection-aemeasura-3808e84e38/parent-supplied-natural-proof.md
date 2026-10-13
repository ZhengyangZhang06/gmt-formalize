# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1.projection_field_aemeasurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 7–8 of the parent-supplied proof of imrep_univ_tangent_starProjection_aemeasurable. There, p_x is the orthogonal projection onto the approximate tangent plane. The argument uses only that each p_x is an orthogonal projection, so it is given here for an arbitrary field of subspaces and an arbitrary measure.

Notation. ⟨·,·⟩ is the Euclidean inner product of ℝ^P, and p_x := (K x).starProjection. L(ℝ^P, ℝ^P) carries the operator-norm topology and its Borel σ-algebra (ContinuousLinearMap.instMeasurableSpace = borel).

1. Self-adjointness and idempotence. For every x and all v, w ∈ ℝ^P, ⟨p_x v, w⟩ = ⟨v, p_x w⟩ (Submodule.inner_starProjection_left_eq_right). Also p_x(p_x w) = p_x w, because p_x w ∈ K(x) and p_x fixes K(x) pointwise (Submodule.starProjection_apply_mem, Submodule.starProjection_eq_self_iff).

2. Polarization. Let u, w ∈ ℝ^P. By step 1, ⟨p_x u, w⟩ = ⟨u, p_x w⟩ = ⟨u, p_x(p_x w)⟩ = ⟨p_x u, p_x w⟩. For real vectors a, b we have |a ± b|² = |a|² ± 2⟨a, b⟩ + |b|², so ⟨a, b⟩ = (|a + b|² − |a − b|²)/4. Take a = p_x u and b = p_x w, and use linearity: p_x u ± p_x w = p_x(u ± w). This gives, for every x, ⟨p_x u, w⟩ = (|p_x(u + w)|² − |p_x(u − w)|²)/4.

3. Matrix coefficients are a.e.-measurable. By hypothesis, x ↦ |p_x(u + w)|² and x ↦ |p_x(u − w)|² are μ-AEMeasurable. Differences and constant multiples of AEMeasurable real functions are AEMeasurable. So by step 2, x ↦ ⟨p_x u, w⟩ is μ-AEMeasurable for all u, w ∈ ℝ^P.

4. Basis expansion. Let e_1, …, e_P be the standard orthonormal basis of ℝ^P (EuclideanSpace.basisFun).
- For (a, b) ∈ Fin P × Fin P let L_{ab} ∈ L(ℝ^P, ℝ^P), L_{ab}(v) := ⟨e_a, v⟩e_b.
- Let Λ : ℝ^{Fin P × Fin P} → L(ℝ^P, ℝ^P), Λ(m) := Σ_{a,b} m_{ab}L_{ab}.
- Put g(x) := (⟨p_x e_a, e_b⟩)_{(a,b)} ∈ ℝ^{Fin P × Fin P}.
Fix x and v. Since v = Σ_a ⟨e_a, v⟩e_a, we have p_x v = Σ_a ⟨e_a, v⟩ p_x e_a. Also p_x e_a = Σ_b ⟨e_b, p_x e_a⟩e_b = Σ_b ⟨p_x e_a, e_b⟩e_b. Hence p_x v = Σ_{a,b} ⟨p_x e_a, e_b⟩⟨e_a, v⟩e_b = Λ(g(x))(v). So p_x = Λ(g(x)) for every x.

5. Conclusion. Λ is a finite sum of the continuous linear maps m ↦ m_{ab}L_{ab} (a coordinate projection times a fixed operator). So Λ is continuous linear, hence Borel measurable. g is μ-AEMeasurable as a map into the finite product ℝ^{Fin P × Fin P}, because each of its coordinates is (step 3; AEMeasurable.of_eval). A measurable map composed with a μ-AEMeasurable map is μ-AEMeasurable (Measurable.comp_aemeasurable). Therefore x ↦ p_x = Λ(g(x)) is μ-AEMeasurable. If P = 0, all spaces are trivial and the same argument applies with empty sums. ∎

## Key steps

1. Each p_x is self-adjoint and idempotent, so ⟨p_x u, w⟩ = ⟨p_x u, p_x w⟩ = (|p_x(u+w)|² − |p_x(u−w)|²)/4.
2. Hence every matrix coefficient x ↦ ⟨p_x e_a, e_b⟩ is μ-a.e. measurable.
3. p_x = Λ((⟨p_x e_a, e_b⟩)_{a,b}), where Λ(m) = Σ m_{ab}⟨e_a,·⟩e_b is a continuous linear map on the finite-dimensional coefficient space.
4. A continuous map composed with an a.e.-measurable map into ℝ^{P×P} is a.e.-measurable.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git show cd85cf76069b4253c566d71bc95ea30382f99c75:GMT/Ch07/Submission.lean | cmp - GMT/Ch07/Submission.lean`
- `cat local-references/123e8435b4a2469b/manifest.json`
- `cat nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json}`
- `sed -n 85,280p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, aemeasurable_starProjection_of_approximateTangentField)`
- `sed -n 70,100p book/chapter-03.txt (Definition 1.4, Remarks 1.5)`
- `rg -n 'theorem Isometry.map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety_image|theorem Isometry.euclideanHausdorffMeasure_image' mathlib/Mathlib`
- `rg -n "theorem aemeasurable_of_tendsto_metrizable_ae'|theorem continuousAt_of_dominated|integral_pos_of_hasCompactSupport_nonneg_nonzero|piLpCongrRight|piLpCongrLeft|theorem measurePreserving|theorem MeasurePreserving.integral_comp" mathlib/Mathlib`
- `rg -n 'starProjection_eq_sum_rankOne|theorem inner_starProjection_left_eq_right|theorem AEMeasurable.of_eval|theorem withDensity_absolutelyContinuous|instance instMeasurableSpace|instance instBorelSpace' mathlib/Mathlib`
- `grep -rhoE '"lean_name": *"[^"]+"' nodes dag.json problem.json | sort | uniq -c (161 distinct names); rg -n -w 'exists_plane_cutoff_quadratic_moment_eq|continuous_blowUp_image_setIntegral|aemeasurable_starProjection_of_aemeasurable_norm_sq' simongmt/Poincare project/GMT mathlib/Mathlib nodes dag.json problem.json DAG.md`
- `python3 scan of nodes/*/*.json for lean_name dtc_cone_tangentProjection_aemeasurable and imrep_approxTangent_starProjection_aesm (their lean_statements)`
- `lake env lean /tmp/tpa-v2/Stmts.lean (child/parent types, #synth MeasurableSpace/BorelSpace on Euclid P →L[ℝ] Euclid P, rfl to borel, pp.explicit #check); lake env lean /tmp/tpa-v2/Assembly.lean; lake env lean /tmp/tpa-v2/Full.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/tmp/tpa-v2/Stmts.lean`
- `/tmp/tpa-v2/Assembly.lean`
- `/tmp/tpa-v2/Full.lean`

Contract and Submission:
- The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.
- The parent's dispatch commit cd85cf76 leaves Submission.lean unchanged, so no Submission declaration can collide with the child names.

SimonGMT:
- Chapter03/Rectifiable.lean defines blowUpMap x r y = r⁻¹(y−x).
- It defines HasApproximateTangentSpaceAt as finrank = n plus convergence for every C_c test function as r → 0⁺. This is Simon Ch. 3, Def. 1.4 (chapter-03.txt lines 77–86).
- It proves uniqueness of the tangent plane but not measurability of the tangent-plane field, so the three children are new obligations.

Mathlib snapshot:
- It supplies every lemma the child proofs cite: Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_homothety_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, LinearIsometryEquiv.piLpCongrLeft / piLpCongrRight, LinearIsometryEquiv.measurePreserving, MeasurePreserving.integral_comp, Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero, continuousAt_of_dominated, aemeasurable_of_tendsto_metrizable_ae', OrthonormalBasis.starProjection_eq_sum_rankOne, Submodule.inner_starProjection_left_eq_right, AEMeasurable.of_eval and withDensity_absolutelyContinuous.
- ContinuousLinearMap.instMeasurableSpace is borel _. It is the instance used in both the parent type and child C.

Lean checks:
- All three child types elaborate after `import GMT.Ch07.Submission`.
- The conditional assembly compiles; its sorryAx comes only from the sorry'd children.
- Full.lean (sha256 5f31f5e9…) proves the three children at their exact frozen types and the parent from them. All four use only propext, Classical.choice and Quot.sound.

Names:
- exists_plane_cutoff_quadratic_moment_eq is new everywhere.
- continuous_blowUp_image_setIntegral and aemeasurable_starProjection_of_aemeasurable_norm_sq occur only in this node's rejected v1 files, with identical types.
- The nearest DAG statements are different propositions: imrep_approxTangent_starProjection_aesm (AEStronglyMeasurable, general U, Hⁿ⌞M) and dtc_cone_tangentProjection_aemeasurable (general U, Hⁿ⌞M).
