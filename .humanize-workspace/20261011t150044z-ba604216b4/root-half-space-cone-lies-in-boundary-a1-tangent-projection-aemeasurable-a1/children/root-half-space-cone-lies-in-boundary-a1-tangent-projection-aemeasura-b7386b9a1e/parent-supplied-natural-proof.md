# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1.plane_quadratic_moment-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent-supplied proof of imrep_univ_tangent_starProjection_aemeasurable, which sets c_n := ∫_{ℝⁿ} χ(|z|²) z_1² dz with χ(t) = max(1 − t, 0). That proof establishes the measurability of the approximate tangent planes of Simon Ch. 3, Definition 1.4 (chapter-03.txt lines 77–86), which Simon uses implicitly. Simon prints no proof of this computation, so the parent's argument is reproduced here with all details. The constant is defined on ℝⁿ alone, before any ambient dimension is chosen; this is why one constant serves every P.

Notation. Fix n ≥ 1. Hⁿ := μHE[n], on ℝ^P for each P and on ℝⁿ. For a set A, ∫_A g dHⁿ means ∫ g d(Hⁿ⌞A). E_n := ℝⁿ = EuclideanSpace ℝ (Fin n), with Lebesgue measure Lⁿ (volume). Since n ≥ 1, the index i₀ := 0 ∈ Fin n exists. For i, j ∈ Fin n and z ∈ E_n put h_{ij}(z) := max(1 − |z|², 0)·z_i·z_j, and define c := ∫_{E_n} h_{i₀i₀} dLⁿ. Only n enters this definition: c does not depend on any ambient dimension P, subspace Q or vector u.

1. Integrability. Each h_{ij} is continuous: it is built from the norm, the coordinate maps, max and products. If |z| > 1 then 1 − |z|² < 0, so max(1 − |z|², 0) = 0 and h_{ij}(z) = 0. Hence h_{ij} has support in the closed unit ball, which is compact. Lⁿ is finite on compact sets, so a continuous compactly supported function is Lⁿ-integrable (Continuous.integrable_of_hasCompactSupport).

2. Off-diagonal moments vanish. Let i ≠ j. Let S : E_n → E_n negate the i-th coordinate: (Sz)_k = −z_k for k = i and (Sz)_k = z_k for k ≠ i. In Lean this is LinearIsometryEquiv.piLpCongrRight 2 with −id in slot i and id elsewhere.
- S is a linear isometry equivalence, so |Sz| = |z|.
- S preserves Lⁿ (LinearIsometryEquiv.measurePreserving).
- Being a homeomorphism, S is a measurable embedding.
Since (Sz)_i = −z_i and (Sz)_j = z_j, we get h_{ij}(Sz) = −h_{ij}(z) for all z. By change of variables for measure-preserving embeddings (MeasurePreserving.integral_comp), ∫ h_{ij} dLⁿ = ∫ h_{ij}(Sz) dLⁿ(z) = −∫ h_{ij} dLⁿ. Hence ∫ h_{ij} dLⁿ = 0.

3. Diagonal moments are all equal to c. Fix i. Let T : E_n → E_n permute the coordinates by the transposition σ = swap(i₀, i), so (Tz)_k = z_{σ(k)}. In Lean this is LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i₀ i).
- T is a linear isometry equivalence, so |Tz| = |z|, and T preserves Lⁿ.
- (Tz)_i = z_{σ(i)} = z_{i₀}.
Hence h_{ii}(Tz) = max(1 − |z|², 0)·z_{i₀}² = h_{i₀i₀}(z). By change of variables, ∫ h_{ii} dLⁿ = ∫ h_{ii}(Tz) dLⁿ(z) = ∫ h_{i₀i₀} dLⁿ = c.

4. c > 0. The function h_{i₀i₀} = max(1 − |z|², 0)·z_{i₀}² is ≥ 0 everywhere and is continuous with compact support (step 1). At z* := (1/2)e_{i₀} we have |z*|² = 1/4, so h_{i₀i₀}(z*) = (3/4)(1/4) = 3/16 ≠ 0. Lⁿ is positive on nonempty open sets and finite on compacts. So the integral of a nonnegative, continuous, compactly supported function that is nonzero at some point is positive (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero). Thus c > 0. The constant c is now fixed; everything below holds with this same c.

5. Parametrizing Q. Now let P ∈ ℕ be arbitrary, let Q ⊆ ℝ^P be a linear subspace with dim Q = n, and let u ∈ ℝ^P. (If n > P there is no such Q, and nothing has to be proved.) Choose an orthonormal basis τ_1, …, τ_n of Q indexed by Fin n, for example stdOrthonormalBasis ℝ Q reindexed along finrank Q = n. Let ι : E_n → ℝ^P, ι(z) := Σ_i z_i τ_i. This is the inclusion Q → ℝ^P composed with the inverse of the basis' coordinate isometry. By orthonormality, ι is a linear isometry (|ι z| = |z|). Its range is exactly Q: every q ∈ Q equals ι of its coordinate vector, and every Σ z_i τ_i lies in Q.

6. Push-forward of Hausdorff measure.
- Because ι is an isometry, the push-forward of Hⁿ on E_n under ι equals Hⁿ⌞(range ι) = Hⁿ⌞Q (Isometry.map_euclideanHausdorffMeasure).
- Hⁿ on E_n = EuclideanSpace ℝ (Fin n) is Lⁿ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
- An isometry defined on a complete space is a closed embedding, hence a measurable embedding.
Therefore, writing F(y) := max(1 − |y|², 0)⟨u, y⟩², we get ∫_Q F dHⁿ = ∫ F d(ι_#Lⁿ) = ∫_{E_n} F(ι z) dLⁿ(z) (MeasurableEmbedding.integral_map).

7. Expanding the integrand. Let a_i := ⟨u, τ_i⟩. Then |ι z| = |z| and ⟨u, ι z⟩ = Σ_i z_i a_i. So for every z ∈ E_n, F(ι z) = max(1 − |z|², 0)(Σ_i a_i z_i)² = Σ_i Σ_j a_i a_j h_{ij}(z).

8. Integrating. The finitely many functions a_i a_j h_{ij} are all integrable (step 1), so the integral is additive and homogeneous: ∫_{E_n} F(ι z) dLⁿ = Σ_i Σ_j a_i a_j ∫ h_{ij} dLⁿ. For fixed i, steps 2 and 3 show that only the term j = i survives, and it equals a_i²·c. Hence ∫_Q F dHⁿ = c·Σ_i a_i².

9. Identifying Σ_i a_i². The orthogonal projection onto Q is p_Q v = Σ_i ⟨τ_i, v⟩τ_i (expansion in an orthonormal basis of Q; OrthonormalBasis.starProjection_eq_sum_rankOne). p_Q is self-adjoint (Submodule.inner_starProjection_left_eq_right) and idempotent (p_Q u ∈ Q is fixed by p_Q). Therefore |p_Q u|² = ⟨p_Q u, p_Q u⟩ = ⟨u, p_Q(p_Q u)⟩ = ⟨u, p_Q u⟩ = Σ_i ⟨τ_i, u⟩⟨u, τ_i⟩ = Σ_i a_i².

10. Conclusion. By steps 6–9, ∫_Q max(1 − |y|², 0)⟨u, y⟩² dHⁿ(y) = c|p_Q u|². The constant c > 0 was fixed in the Notation paragraph and step 4, before P, Q and u were chosen in step 5. So one and the same c works for every P ∈ ℕ, every n-dimensional subspace Q ⊆ ℝ^P and every u ∈ ℝ^P, which is exactly the claim: ∃ c > 0, ∀ P, ∀ Q with dim Q = n, ∀ u, ∫_Q max(1 − |y|², 0)⟨u, y⟩² dHⁿ(y) = c|p_Q u|². ∎

## Key steps

1. Define c := ∫_{ℝⁿ} max(1−|z|²,0) z_{i₀}² dLⁿ(z), which involves only n; every h_{ij}(z) = max(1−|z|²,0)z_iz_j is continuous with support in the closed unit ball, hence integrable.
2. Coordinate reflections (linear isometries preserving Lebesgue measure) give ∫h_{ij} = 0 for i ≠ j; coordinate swaps give ∫h_{ii} = c.
3. c > 0: the integrand is continuous, ≥ 0, compactly supported and equals 3/16 at e_{i₀}/2.
4. For arbitrary P, Q ⊆ ℝ^P with dim Q = n and u ∈ ℝ^P: an orthonormal basis τ of Q gives a linear isometry ι : ℝⁿ → ℝ^P onto Q with ι_#Lⁿ = Hⁿ⌞Q, so ∫_Q f_u dHⁿ = ∫ f_u∘ι dLⁿ.
5. f_u∘ι = Σ_{i,j} a_ia_j h_{ij} with a_i = ⟨u,τ_i⟩, so the integral is cΣa_i² = c|p_Q u|², with the same c (fixed before P, Q, u) for all P, Q, u.

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
