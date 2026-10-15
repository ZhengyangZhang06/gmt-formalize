# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.slice_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 2 and 3 of the parent proof, for one fixed t.
Notation: ω̂ := (ω : DifferentialForm (Euclid P) n'); β_a := (z ↦ flatF a(ω̂(z))); γ := (z ↦ flat(ω̂(z))); δ_a := (z ↦ fderiv ℝ β_a z (g a)).
1. Test forms.
- ω̂ is a test form (ω.property.1).
- β_a and γ are test forms by Submission.dimred_cs_sos_mt_interior_product (b) with translation 0 (rewriting 0 + z = z).
- Each δ_a is a test form by the sibling Submission.dimred_cs_sos_mt_cs_isTestForm_fderiv_apply.
- dγ and dω̂ are test forms by exteriorDerivative_isTestForm.
Applying interior_product (b) once more (with Φ := id on Λ^{m+1} and translation t for δ_a and dγ, and with Φ := flatD and translation t for dω̂), the forms F := (y ↦ flatD(dω̂(t + y))), A_a := (y ↦ δ_a(t + y)) and D := (y ↦ dγ(t + y)) are test forms. All have support in univ.
2. Pointwise identity. ω̂ is C^∞, hence differentiable at every point. For each y, apply the sibling Submission.dimred_cs_sos_mt_cs_flat_extDeriv_split at x := t + y, with the given g, h, h₁, h₂, flatD, flat, flatF and the three contraction identities. It gives
flatD(dω̂(t + y)) = Σ_a (−1)^a • δ_a(t + y) + (−1)^{j+1} • dγ(t + y).
Hence, in TestFormOn univ (m + 1),
⟨F, _⟩ = Σ_a (−1)^a • ⟨A_a, _⟩ + (−1)^{j+1} • ⟨D, _⟩
(Subtype.ext; the coercions Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul are pointwise).
3. Linearity. For a test form ψ with support in univ, currentEval Y ψ = Y ⟨ψ, _⟩ (the positive branch of the definition of currentEval). Y.toCurrent is ℝ-linear, so by step 2 (map_add, map_sum, map_smul, smul_eq_mul)
currentEval Y F = Σ_a (−1)^a · currentEval Y A_a + (−1)^{j+1} · currentEval Y D.
4. Boundary term. Apply the sibling Submission.dimred_cs_sos_mt_cs_translate_boundary_eval with the test m-form γ, this t and Y.boundary = X:
currentEval Y D = currentEval X (y ↦ γ(t + y)) = currentEval X (y ↦ flat(ω̂(t + y))).
5. Substituting step 4 into step 3 gives the claim, since A_a is literally y ↦ fderiv ℝ (z ↦ flatF a(ω̂(z))) (t + y) (g a). ∎

## Key steps

1. The forms y ↦ D_{g_a}β_a(t + y), y ↦ dγ(t + y) and y ↦ flatD(dω̂(t + y)) are test forms (interior_product (b), isTestForm_fderiv_apply, exteriorDerivative_isTestForm)
2. Pointwise identity at t + y from flat_extDeriv_split, read as an identity in TestFormOn univ (m+1)
3. Linearity of Y on test forms (currentEval agrees with Y on test forms)
4. Boundary term by translate_boundary_eval

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1, mathlib 25730c7c); diff snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Submission.lean and GMT/Ch07/Contract.lean (both identical); git rev-parse HEAD = b4d606db1`
- `python3 over dag.json: selected node record (depth 5; runtime.py _decompose splits while depth < max_depth = 6), lean_statements and statuses of interior_product / frame_measure / slice_integrable (decomposing) and translate_derivative (accepted, dimred_cs_ti_translate_action_hasDerivAt), parent decomposition-v1.json`
- `python3 collision check of the nine proposed names dimred_cs_sos_mt_cs_{isTestForm_fderiv_apply, flat_extDeriv_split, translate_boundary_eval, slice_identity, slice_hasDerivAt, frame_box_compact, frame_box_integral, coord_box_ftc, frame_box_ftc} against all 2417 dag.json lean_names (0 matches) and against the node proof base 77e7ccf GMT/Ch07/Submission.lean (0 matches)`
- `grep -n -i "insertNth|piFinSuccAbove|HasDerivAt|integral_eq_sub|exteriorDerivative (fun|extDeriv" over all dag.json lean_statements (found cmcdt_cbm_st_slice_integral and cmcdtfrcb_cube_partial_ftc: open unit cubes in Euclid (k+1) with ContDiff G, not reusable with identical types here)`
- `grep -n over SimonGMT Chapter06/Forms.lean and Currents.lean: IsTestForm, exteriorDerivative, exteriorDerivative_apply, exteriorDerivative_isTestForm, tsupport_exteriorDerivative_subset, testFormOnSubmodule, exteriorDerivativeTestOn, GeometricCurrentOn.boundary(_apply); grep -n currentEval in GMT/Ch07/Submission.lean`
- `rg -n over snapshot mathlib: def extDeriv, extDeriv_apply, fderiv_comp_add_left, fderiv_continuousAlternatingMap_apply_const_apply, Fin.append_left, Fin.append_right, Fin.insertNthEquiv, MeasurableEquiv.piFinSuccAbove, measurePreserving_piFinSuccAbove, MeasurableEmbedding.setIntegral_map, MeasurableEmbedding.integrableOn_map_iff, LinearMap.isClosedEmbedding_of_injective, Fintype.linearCombination, Orthonormal.inner_right_fintype, Submodule.mem_span_range_iff_exists_fun, setIntegral_prod, setIntegral_prod_swap, ContinuousOn.integrableOn_compact, Continuous.finInsertNth, intervalIntegral.integral_eq_sub_of_hasDerivAt, integral_Icc_eq_integral_Ioc`
- `grep -n "μHE|euclideanHausdorffMeasure" Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_zero: μHE[0] = μH[0], so for j = 0 the face Q'_a = {0} has mass 1, consistent with frame_measure (i))`
- `read runtime.py (_decompose depth gate, _existing_lean_name_problem, _dependency_problem) and inherited.py (cited_inherited: children inherit interior_product, frame_measure, deriv_translate by exact-name citation)`
- `lean v4.35.0-rc3 with LEAN_PATH = local copies of the pinned build: /tmp/cs-decomp/check/{Types,Assembly,Children,Child1,Child6}.lean and /tmp/cs-decomp/final/Final.lean (generated from the exact lean_statements below)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-90e5cf2d92/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-90e5cf2d92/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-90e5cf2d92/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/tmp/cs-decomp/check/Types.lean`
- `/tmp/cs-decomp/check/Assembly.lean`
- `/tmp/cs-decomp/check/Children.lean`
- `/tmp/cs-decomp/check/Child1.lean`
- `/tmp/cs-decomp/check/Child6.lean`
- `/tmp/cs-decomp/final/Final.lean`

Pins match. The snapshot manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c, and the snapshot Contract.lean equals the workspace Contract.lean and Submission.lean. The parent's frozen type equals the handoff lean_statement byte for byte.

Library facts. SimonGMT supplies the needed current-level API:
- exteriorDerivative = extDeriv and exteriorDerivative_apply;
- exteriorDerivative_isTestForm and exteriorDerivativeTestOn;
- GeometricCurrentOn.boundary_apply.
currentEval is the contract's evaluation on test forms. Snapshot mathlib has every analytic tool the children use (exact names in the queries):
- fderiv_comp_add_left (translation commutes with d);
- fderiv_continuousAlternatingMap_apply_const_apply and Fin.append_left / append_right (the index identity);
- MeasurableEmbedding.setIntegral_map, LinearMap.isClosedEmbedding_of_injective and Orthonormal.inner_right_fintype (frame coordinates);
- measurePreserving_piFinSuccAbove, setIntegral_prod(_swap) and intervalIntegral.integral_eq_sub_of_hasDerivAt (Fubini and FTC).
μHE[0] = μH[0], so the j = 0 faces are points of mass 1.

Reuse. No accepted DAG declaration has the type of any proposed child. The accepted deformation-theorem lemmas cmcdt_cbm_st_slice_integral and cmcdtfrcb_cube_partial_ftc are about open unit cubes in Euclid (k+1) with ContDiff G; here only directional derivatives of slice functions are available. So new names are used, and none collides (dag.json, proof base 77e7ccf). Children inherit the parent's dependencies by exact-name citation (inherited.py):
- Submission.dimred_cs_sos_mt_interior_product (translate_boundary, slice_identity, slice_deriv);
- Submission.dimred_cs_sos_mt_frame_measure (frame_box_integral);
- Submission.dimred_cs_ti_translate_action_hasDerivAt (slice_deriv).

Lean checks.
- All nine child types elaborate after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract opens.
- Final.lean, generated from these exact strings, proves every child and the frozen parent with sorry only in the stubs of the parent's four resolved dependencies.
- isTestForm_fderiv_apply, flat_extDeriv_split, frame_box_compact and coord_box_ftc have axioms [propext, Classical.choice, Quot.sound].
- The other children and the parent use only those four stubs and sibling children.
