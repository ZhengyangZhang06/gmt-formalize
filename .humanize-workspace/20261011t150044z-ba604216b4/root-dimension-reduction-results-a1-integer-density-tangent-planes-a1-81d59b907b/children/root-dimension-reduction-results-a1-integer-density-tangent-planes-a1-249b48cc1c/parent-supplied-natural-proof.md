# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_area-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_area-a1.prod_area-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 5, 6 and 7 of the supplied cone_area proof (transport ℝ × ℝ ↔ Euclid 2, area formula, Gram determinant of two vectors, transport back), stated for a general injective immersion G of a measurable R ⊆ ℝ × ℝ. The area formula itself is the sibling gram_area (Submission.codim1_lur_cd_injective_area_formula_gram) with m = 2.
Notation: E₂ := Euclid 2; for w ∈ E₂, w₀ := w 0 and w₁ := w 1; e₀ := EuclideanSpace.single 0 1 and e₁ := EuclideanSpace.single 1 1.

1. (Coordinate isomorphism.) Let e : E₂ → ℝ × ℝ, e(w) := (w₀, w₁). It is realized as the continuous linear equivalence (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ), so e w = (w 0, w 1) holds definitionally. e is bijective, linear and continuous, and e(e₀) = (1, 0), e(e₁) = (0, 1).

2. (e preserves Lebesgue measure.) As a function, e = finTwoArrow ∘ (toLp 2)⁻¹. Composing EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2) with volume_preserving_finTwoArrow ℝ shows that e is measure preserving from volume on E₂ to volume (the product Lebesgue measure) on ℝ × ℝ. Being a homeomorphism, e is a measurable embedding.

3. (Pull back to E₂.) Let G̃ := G ∘ e : E₂ → ℝ^P and F := e⁻¹(R). F is measurable, since e is continuous and R is measurable.
- Chain rule for a continuous linear equivalence (ContinuousLinearEquiv.comp_right_fderiv): DG̃(w) = DG(e w) ∘ e for every w ∈ E₂, with no differentiability assumption.
- For w ∈ F we have e w ∈ R, so G is differentiable at e w. Hence G̃ is differentiable at w (composition with the differentiable linear map e), and DG̃(w) = DG(e w) ∘ e is injective as a composition of injective maps.
- G̃ is injective on F: if w, w′ ∈ F and G(e w) = G(e w′), injectivity of G on R gives e w = e w′, and injectivity of e gives w = w′.

4. (Image.) e is surjective, so e(e⁻¹(R)) = R and G̃(F) = G(e(e⁻¹(R))) = G(R) (Set.image_comp, Set.image_preimage_eq).

5. (Area formula.) Apply the sibling gram_area with m = 2, map G̃, Borel set F and integrand h; its hypotheses are step 3. Together with step 4 this gives
∫_{G(R)} h dμHE[2] = ∫_{G̃(F)} h dμHE[2] = ∫_F (det M(w))^{1/2} · h(G̃ w) dw,
where M(w) is the 2×2 matrix with entries M(w)_{ij} = ⟨DG̃(w)e_i, DG̃(w)e_j⟩ and dw is volume on E₂.

6. (Gram determinant of two vectors.) Fix w ∈ E₂ and put q := e w, a := DG(q)(1, 0), b := DG(q)(0, 1).
- By steps 3 and 1, DG̃(w)e₀ = DG(q)(e e₀) = a and DG̃(w)e₁ = DG(q)(e e₁) = b.
- Hence det M(w) = M₀₀M₁₁ − M₀₁M₁₀ = ⟨a, a⟩⟨b, b⟩ − ⟨a, b⟩⟨b, a⟩ = ‖a‖²‖b‖² − ⟨a, b⟩² (Matrix.det_fin_two, ⟨x, x⟩ = ‖x‖², symmetry of the real inner product).
- Also G̃ w = G q.
So for every w ∈ E₂ the integrand of step 5 equals Ψ(e w), where
Ψ(q) := (‖DG(q)(1, 0)‖²‖DG(q)(0, 1)‖² − ⟨DG(q)(1, 0), DG(q)(0, 1)⟩²)^{1/2} · h(G q).

7. (Back to ℝ × ℝ.) Since e is measure preserving and a measurable embedding, MeasurePreserving.setIntegral_preimage_emb gives ∫_{e⁻¹(R)} Ψ(e w) dw = ∫_R Ψ(q) dq. Combining steps 5–7, ∫_{G(R)} h dμHE[2] = ∫_R Ψ(q) dq, which is the claim. Every step is an equality of Bochner integrals: integrands were rewritten pointwise and the measure was transported, so no integrability hypothesis is needed. ∎

Formalization notes. A complete Lean proof of this exact type, using only the sibling Submission.codim1_lur_cd_injective_area_formula_gram and the frozen import closure, compiles.
- let e : Euclid 2 ≃L[ℝ] ℝ × ℝ := (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ), with he : ∀ w, e w = (w 0, w 1) := fun w => rfl.
- hmp : MeasurePreserving e volume volume := (volume_preserving_finTwoArrow ℝ).comp (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).
- hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding.
- Measurability of e ⁻¹' R: e.continuous.measurable hR.
- hfd : ∀ w, fderiv ℝ (G ∘ e) w = (fderiv ℝ G (e w)).comp (e : Euclid 2 →L[ℝ] ℝ × ℝ) := fun w => e.comp_right_fderiv.
- Image: rw [Set.image_comp, Set.image_preimage_eq R e.surjective].
- Apply the sibling to P 2 (G ∘ e) (e ⁻¹' R), with:
  differentiability (hG (e w) hw).comp w e.differentiableAt;
  injectivity (by rw [hfd]; exact (hreg (e w) hw).comp e.injective);
  InjOn e.injective (hinj hw hw' heq).
- Integrand: e (EuclideanSpace.single 0 1) = (1, 0) and e (EuclideanSpace.single 1 1) = (0, 1), each by rw [he]; simp. Then simp only [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Matrix.det_fin_two, Matrix.of_apply, Function.comp_apply, real_inner_self_eq_norm_sq, real_inner_comm (fderiv ℝ G (e w) (1, 0))] followed by ring_nf.
- Finish: simp_rw the pointwise identity, then hmp.setIntegral_preimage_emb hemb Ψ R. Give Ψ explicitly; an underscore leaves a stuck NormedSpace instance.

## Key steps

1. e : Euclid 2 ≃L[ℝ] ℝ × ℝ, e w = (w 0, w 1), is a volume-preserving measurable embedding (volume_preserving_finTwoArrow composed with EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp).
2. G̃ = G ∘ e on F = e⁻¹(R): G̃ is differentiable, DG̃(w) = DG(e w) ∘ e is injective, G̃ is injective on F, and G̃(F) = G(R) because e is surjective.
3. Sibling gram_area with m = 2: ∫_{G(R)} h dμHE[2] = ∫_F √det[⟨DG̃(w)e_i, DG̃(w)e_j⟩] · h(G̃ w) dw.
4. DG̃(w)e₀ = DG(e w)(1, 0) and DG̃(w)e₁ = DG(e w)(0, 1); det_fin_two gives ‖a‖²‖b‖² − ⟨a, b⟩², so the integrand is Ψ(e w).
5. MeasurePreserving.setIntegral_preimage_emb: ∫_{e⁻¹R} Ψ∘e = ∫_R Ψ.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git show <this node's proof branch>:GMT/Ch07/Submission.lean | grep '^theorem Submission.'`
- `python3 -I scans of dag.json: lean_name matching area_formula|cone_area|idtp_ccd_scsp|areaJac|gram, with status/candidate_commit/lean_statement; the exact lean_statement and title of codim1_lur_cd_injective_area_formula_gram; cross-parent children/depends_on reuse counts`
- `grep -c/grep -rl for idtp_ccd_scsp_ca_prod_area_formula, idtp_ccd_scsp_ca_cone_map_regular and idtp_ccd_scsp_ca_ in dag.json, runs/.../nodes and ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match)`
- `rg -n 'theorem volume_preserving_finTwoArrow|volume_preserving_symm_measurableEquiv_toLp|theorem comp_right_fderiv|setIntegral_preimage_emb|theorem det_fin_two |def finTwoArrow|euclideanHausdorffMeasure_eq_volume|theorem HasFDerivAt.smul |theorem HasFDerivAt.comp |theorem setIntegral_congr_fun |theorem image_preimage_eq |EuclideanSpace.equiv|lemma smul_right_injective|theorem Ioo_mem_nhds|theorem real_inner_self_eq_norm_sq|theorem real_inner_smul_right|theorem normDet_sq_eq_det_gram' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'area_formula|areaJacobian|normDet|finTwoArrow' local-references/123e8435b4a2469b/project`
- `lake env lean /tmp/cone_area_check/Closure.lean (#check LinearMap.normDet, LinearMap.normDet_sq_eq_det_gram, LinearMap.euclideanHausdorffMeasure_image, integral_image_eq_integral_abs_det_fderiv_smul, volume_preserving_finTwoArrow, MeasurePreserving.setIntegral_preimage_emb, Matrix.det_fin_two, ContinuousLinearEquiv.finTwoArrow, EuclideanSpace.equiv after import GMT.Ch07.Submission)`
- `grep -n 'def check_source_delta' -A 35 /runtime/flows/gmt-claude-82aee5f72857/_recursive_lean/leaf_verification.py; grep -n '_machine_leaf|_existing_lean_name_problem|existing_by_name|_install_parent_supplied_child_handoff|_accepted_checkpoint' /runtime/flows/gmt-claude-82aee5f72857/_recursive_lean/runtime.py; check_parent_git_delta in parent_verification.py; swarm-project.json (leaf_lean_agent_review=false, max_depth=6)`
- `git show 15f8046553cb9af46b3f645a487e52fb756a62ac:GMT/Ch07/Submission.lean > /tmp/cone_area_check/A_accepted.lean; lake env lean A_accepted.lean with #print axioms; cat nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-dad7016689/{isolated-comparator-result.json,accepted-candidate.json,parent-child-handoff.json}`
- `lake env lean /tmp/cone_area_check/Stubs.lean, ChildB.lean, ChildC.lean, EndToEnd.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-81d59b907b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-81d59b907b/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-dad7016689/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-dad7016689/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-dad7016689/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Equiv/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Torsion/Free.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/runtime/flows/gmt-claude-82aee5f72857/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-82aee5f72857/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-82aee5f72857/_recursive_lean/parent_verification.py`
- `/tmp/cone_area_check/Closure.lean`
- `/tmp/cone_area_check/A_accepted.lean`
- `/tmp/cone_area_check/Stubs.lean`
- `/tmp/cone_area_check/ChildB.lean`
- `/tmp/cone_area_check/ChildC.lean`
- `/tmp/cone_area_check/EndToEnd.lean`

Pins match. Snapshot project_commit b4d606d equals workspace HEAD, mathlib 25730c7c equals .lake/packages/mathlib HEAD, and SimonGMT is at the lakefile pin 2b36630. The snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and this node's proof base adds no declarations.

Blocking finding for an unsplit leaf. After `import GMT.Ch07.Submission`, LinearMap.normDet, LinearMap.normDet_sq_eq_det_gram and LinearMap.euclideanHausdorffMeasure_image are unknown constants. SimonGMT Chapter02.WeightedArea is outside the frozen closure, and the machine-leaf gate check_source_delta forbids `import` in leaf deltas. So supplied step 5 cannot be implemented by a leaf as written.

Reuse. DAG node ...chart_divergence-a1.gram_area_formula-a1 (Submission.codim1_lur_cd_injective_area_formula_gram) has status accepted at candidate 15f8046553cb, and its isolated comparator passed. Its accepted source adds one theorem to the frozen base and compiles here with axioms [propext, Classical.choice, Quot.sound]. Its lean_statement is copied byte-for-byte, which satisfies the controller's rule for reusing an accepted theorem with an identical type.

No-match results. rg finds area_formula/areaJacobian/normDet only in the snapshot GMT/Ch02 contract and README, which Ch07 does not import. No DAG node states an area formula over ℝ × ℝ or regularity of the cone map. The new names have no match in dag.json, the run nodes, or any worktree Submission.lean.

Mathlib lemmas used by the children, all in the frozen closure (snapshot locations):
- volume_preserving_finTwoArrow (MeasureTheory/Constructions/Pi.lean:874)
- EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Measure/Haar/InnerProductSpace.lean:124)
- ContinuousLinearEquiv.comp_right_fderiv (Calculus/FDeriv/Equiv.lean:227)
- MeasurePreserving.setIntegral_preimage_emb (Integral/Bochner/Set.lean:571)
- Matrix.det_fin_two (Matrix/Determinant/Basic.lean:809)
- ContinuousLinearEquiv.finTwoArrow (Topology/Algebra/Module/Equiv/Pi.lean:145)
- EuclideanSpace.equiv (InnerProductSpace/PiL2.lean:276)
- HasFDerivAt.smul (FDeriv/Mul.lean:72)
- HasFDerivAt.comp (FDeriv/Comp.lean:107)
- setIntegral_congr_fun (Bochner/Set.lean:73)
- Set.image_preimage_eq (Data/Set/Image.lean:429)
- smul_right_injective (Module/Torsion/Free.lean:103)
- Ioo_mem_nhds (Order/OrderClosed.lean:611)
- real_inner_self_eq_norm_sq (InnerProductSpace/Basic.lean:398)
- real_inner_smul_right (InnerProductSpace/Basic.lean:120)
normDet_sq_eq_det_gram (NormDet.lean:303) appears only in the reused proof's library route.

Lean checks:
- The child types elaborate.
- cone_map is fully proved with standard axioms.
- prod_area is proved from the gram_area stub.
- The parent's exact frozen type is proved from the stubs.
- The end-to-end file (accepted gram_area source, cone_map, prod_area, parent) has no sorry, and #print axioms on Submission.idtp_ccd_scsp_cone_area gives [propext, Classical.choice, Quot.sound].
