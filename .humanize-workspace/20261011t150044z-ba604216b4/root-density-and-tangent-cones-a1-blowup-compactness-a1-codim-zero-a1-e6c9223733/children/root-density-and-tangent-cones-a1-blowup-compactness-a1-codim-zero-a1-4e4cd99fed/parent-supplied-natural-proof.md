# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_density-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_density-a1.det_covector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the notation paragraph, step 2 and the determinant part of step 3 of the parent proof of dtc_bc_cz_top_density (the density part of the Constancy Theorem, Simon Ch. 6, 2.34), with all details filled in. No sibling is used.
Notation. ℝⁿ := Euclid n = EuclideanSpace ℝ (Fin n). An n-covector is an element of Covector (Euclid n) n = Euclid n [⋀^Fin n]→L[ℝ] ℝ, i.e. a continuous alternating n-linear form on ℝⁿ. Let b := EuclideanSpace.basisFun (Fin n) ℝ, an orthonormal basis of ℝⁿ indexed by Fin n, and e := ⇑b. Write b.toBasis for the underlying basis; ⇑b.toBasis = ⇑b = e (OrthonormalBasis.coe_toBasis).
1. Let D := b.toBasis.det : Euclid n [⋀^Fin n]→ₗ[ℝ] ℝ be the determinant alternating form with respect to b.toBasis. By Module.Basis.det_self, D(e) = 1.
2. D is continuous as a map (Fin n → ℝⁿ) → ℝ.
   - By Module.Basis.det_apply, D(v) = det(b.toBasis.toMatrix v).
   - The (i, j) entry of b.toBasis.toMatrix v is b.toBasis.repr (v j) i (Module.Basis.toMatrix_apply), which equals (b.toBasis.coord i)(v j) (Module.Basis.coord_apply).
   - The coordinate functional b.toBasis.coord i is a linear map on the finite-dimensional space ℝⁿ, hence continuous (LinearMap.continuous_of_finiteDimensional), and v ↦ v j is continuous (continuous_apply).
   - So every entry is continuous in v, and the matrix-valued map v ↦ b.toBasis.toMatrix v is continuous (continuous_pi twice).
   - The determinant of a continuous matrix-valued map is continuous (Continuous.matrix_det).
3. Let ε be the continuous alternating map whose underlying alternating map is D and whose continuity is step 2 (in Lean: { D with cont := hcont }). Then ε ∈ Covector (Euclid n) n and ε(v) = D(v) for every v (definitionally). By step 1, ε(e) = 1; this is property (i).
4. Property (ii). Let α be an n-covector and v : Fin n → ℝⁿ. Apply Mathlib's AlternatingMap.eq_smul_basis_det to the basis b.toBasis and to the alternating map α.toAlternatingMap underlying α. It gives α.toAlternatingMap = α(e) • D. Evaluating both sides at v gives α(v) = α(e)·D(v) = ε(v)·α(e).
5. Property (iii). Let τ : Fin n → ℝⁿ be orthonormal with span(range τ) = ⊤.
   - Then ⊤ ≤ span(range τ), so B := OrthonormalBasis.mk hτ (this inequality) is an orthonormal basis of ℝⁿ indexed by Fin n, with ⇑B = τ (OrthonormalBasis.coe_mk).
   - By Mathlib's OrthonormalBasis.det_to_matrix_orthonormalBasis_real b B, the change-of-basis determinant between two orthonormal bases of a real inner product space is ±1: b.toBasis.det ⇑B = 1 ∨ b.toBasis.det ⇑B = −1.
   - That is, D(τ) = 1 ∨ D(τ) = −1, i.e. ε(τ) = 1 ∨ ε(τ) = −1.
6. Steps 3–5 show that ε has the three required properties. ∎
Implementation note (not part of the proof): name every auxiliary Lean declaration introduced for this child with the prefix dtc_bc_cz_top_density_det_covector_ (for example dtc_bc_cz_top_density_det_covector_aux). The candidates of sibling children are merged into one Submission.lean, and only byte-identical duplicate declarations are dropped during that merge.

## Key steps

1. Let D := b.toBasis.det for b = EuclideanSpace.basisFun (Fin n) ℝ. Then D(e) = 1 (Module.Basis.det_self).
2. D is continuous: D(v) = det(b.toBasis.toMatrix v) (det_apply), the coordinates are continuous, and Continuous.matrix_det applies. So ε := { D with cont } is an n-covector with ε(e) = 1.
3. AlternatingMap.eq_smul_basis_det gives α = α(e)•D, hence α(v) = ε(v)·α(e) for all α and v.
4. An orthonormal τ spanning ⊤ gives B := OrthonormalBasis.mk with ⇑B = τ. Then det_to_matrix_orthonormalBasis_real gives ε(τ) = D(τ) = ±1.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/{Contract,Submission}.lean against workspace GMT/Ch07/{Contract,Submission}.lean (identical); grep scope commands (open/namespace/noncomputable section/end) of Contract.lean`
- `python3 -I over dag.json: this node's record (depth 4, status decomposing, children []); siblings under codim_zero-a1; regex scans of lean_statements for basisFun, IsUnitOrientationOf, Orthonormal, finrank, '∃ ε : Covector', 'R.orient y α = σ y', 'R.action ω = ∫ y'; statements of dgcr_unitOrientation_eq_or_neg, rsdic_unitOrientation_eq_or_eq_neg, fvmb_imrep_ae_unitOrientation_approxTangentPlane, dorag_aa_ae_finrank_approxTangentPlane, dgoj_exists_det_covector`
- `rg -n 'euclideanHausdorffMeasure_eq_volume|theorem eq_smul_basis_det|det_to_matrix_orthonormalBasis_real|theorem eq_top_of_finrank_eq|theorem det_self|theorem det_apply' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'continuous_of_finiteDimensional|def mkContinuous|toContinuousAlternatingMap|structure ContinuousAlternatingMap' in snapshot Mathlib Topology/Algebra/Module and Analysis/Normed/Module/{Alternating,Multilinear}`
- `grep -n HasApproximateTangentSpaceAt simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed simongmt Chapter06/Forms.lean and Currents.lean (Covector, DifferentialForm, TestFormOn, GeometricCurrentOn)`
- `rg -l 'dtc_bc_cz_top_density_' GMT, simongmt/Poincare, snapshot project, dag.json (exit 1, no match); rg -o in nodes/ (only the implementation-note mentions dtc_bc_cz_top_density_ and _aux)`
- `python3 -I /tmp/td-split-7f3a/scripts/gen.py: verifier gmt-compare.py child_modules (contract mode) + lean_contract.validate_lean_statement on the 3 child types and the parent type`
- `lake env lean /tmp/td-split-7f3a/check/{Probe,Stmts,C1,C2,C3,Full,Names2}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-e6c9223733/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/td-split-7f3a/check/Full.lean`
- `/tmp/td-split-7f3a/check/Stmts.lean`
- `/tmp/td-split-7f3a/gen/Challenge_det_covector.lean`
- `/tmp/td-split-7f3a/gen/Challenge_orient_sign.lean`
- `/tmp/td-split-7f3a/gen/Challenge_of_sign.lean`
- `/tmp/td-split-7f3a/gen/Challenge_parent.lean`

Pin: the snapshot contract and submission are byte-identical to the workspace files; the workspace HEAD is b4d606d and the tree is clean.

Library support at the pin, all checked by #check in comparator scope:
- Module.Basis.det_self, det_apply, toMatrix_apply and coord_apply; AlternatingMap.eq_smul_basis_det.
- OrthonormalBasis.mk, coe_mk, coe_toBasis and det_to_matrix_orthonormalBasis_real; LinearMap.continuous_of_finiteDimensional; Continuous.matrix_det.
- SimonGMT HasApproximateTangentSpaceAt.finrank_eq; Submodule.eq_top_of_finrank_eq; finrank_euclideanSpace.
- AEStronglyMeasurable.mk, stronglyMeasurable_mk and ae_eq_mk; ContinuousLinearMap.apply.
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (in the frozen import closure, since μHE is defined in the same file); locallyIntegrableOn_iff; lintegral_indicator; Measure.restrict_restrict; integral_congr_ae; setIntegral_eq_integral_of_forall_compl_eq_zero, which needs no integrability.

Mathlib has no finite-dimensional continuity lemma for multilinear maps. ε is therefore built as { D with cont } from continuity via det_apply.

Lean evidence:
- All three child types and the parent type validate and elaborate in the exact generated challenge files.
- Full.lean proves all three children and the parent from them; every target depends only on propext, Classical.choice and Quot.sound.

Reuse and names:
- No byte-identical accepted reuse exists; dgoj_exists_det_covector is weaker.
- No dtc_bc_cz_top_density_ names exist anywhere.
