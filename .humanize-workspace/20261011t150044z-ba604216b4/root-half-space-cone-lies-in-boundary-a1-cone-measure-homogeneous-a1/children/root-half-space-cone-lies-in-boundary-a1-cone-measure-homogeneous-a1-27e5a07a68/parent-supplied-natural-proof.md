# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1.cone_pullback_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 2 ("By the contract, blowUp C 0 λ is the push-forward of C by the proper affine map η(y) = −λ^{-1}·0 + λ^{-1}y = S(y), acting by (blowUp C 0 λ)(ω) = C(η^#ω) with (η^#ω)(y) = ω(S(y))∘(λ^{-1}id) = λ^{-n}ω(λ^{-1}y) (affinePullbackForm with L = λ^{-1}id, b = 0); η^#ω is again a test form because η is a proper affine isomorphism. The domain of blowUp C 0 λ is dilation 0 λ '' univ = univ, so every test form ω on ℝ^P satisfies the test-form condition in currentEval, and IsConeCurrent C gives (2.1) C(ω) = C(η^#ω)"). Book: Simon 7.3.1(2) (cone: η_{0,λ#}C = C) and Ch. 6, 2.23 (chapter-06.txt line 408: f_#T(ω) = T(f^#ω)); the cone property is used in the proof of 7.4.5 (chapter-07.txt lines 697–698).

Fix λ > 0 and ω ∈ TestFormOn univ n. Put L := dilationCLM P λ = λ^{-1} · id (a continuous linear map of ℝ^P) and b := −(λ^{-1} · 0), so that dilation 0 λ y = b + L y for all y (definition of dilation), and put V := dilation 0 λ '' univ, the domain of blowUp C 0 λ.

1. IsConeCurrent C, applied to λ, the proof of 0 < λ, and ω, gives currentEval (blowUp C 0 λ) ω = C(ω).

2. V = ℝ^P: every x ∈ ℝ^P equals dilation 0 λ (λx), because −(λ^{-1}·0) + λ^{-1}(λx) = 0 + x = x (λ ≠ 0). Hence tsupport ω ⊆ V. Moreover ω is a test form (smooth with compact support; first component of ω.property). So the condition h : IsTestForm ω ∧ tsupport ω ⊆ V in the definition of currentEval holds, the 'if' takes its positive branch, and currentEval (blowUp C 0 λ) ω = (blowUp C 0 λ) ⟨ω, h⟩.

3. By the contract's definition, blowUp C 0 λ = (C.restrictDomain h_sub).affinePushforward L b h_proper, where h_sub is the inclusion (y ↦ b + L y)^{-1}(V) ⊆ univ and h_proper the properness of y ↦ b + Ly (both proved inside the definition of blowUp). By GeometricCurrentOn.affinePushforward_apply and GeometricCurrentOn.restrictDomain_apply (both hold by rfl),
 (blowUp C 0 λ) ⟨ω, h⟩ = C(ω'), where ω' := testFormOnInclusion h_sub n (affinePullbackTestOn L b h_proper V n ⟨ω, h⟩).
 Here ω' is an element of TestFormOn univ n (the SimonGMT constructions affinePullbackTestOn and testFormOnInclusion produce test forms; properness of the affine map is what makes the pulled-back form compactly supported), and its underlying form is (testFormOnInclusion_coe, affinePullbackTestOn_coe, definition of affinePullbackForm)
 ω'(y) = affinePullbackForm L b ω y = (ω(b + L y)).compContinuousLinearMap L for every y ∈ ℝ^P.

4. Combining steps 1–3: C(ω') = (blowUp C 0 λ)⟨ω, h⟩ = currentEval (blowUp C 0 λ) ω = C(ω).

5. Pointwise formula. For every y, b + L y = −(λ^{-1}·0) + λ^{-1}y = λ^{-1}y. Let α := ω(λ^{-1}y), an n-covector, i.e. a continuous alternating n-linear map (ℝ^P)^n → ℝ. For v = (v_1, …, v_n) ∈ (ℝ^P)^n,
 (α.compContinuousLinearMap L)(v) = α(λ^{-1}v_1, …, λ^{-1}v_n) = (∏_{i ∈ Fin n} λ^{-1}) · α(v) = (λ^{-1})^n · α(v),
 by multilinearity (ContinuousAlternatingMap.map_smul_univ: f(c_1v_1, …, c_nv_n) = (∏_i c_i) · f(v); the product over Fin n of the constant λ^{-1} is (λ^{-1})^n by Finset.prod_const and card (Fin n) = n). By extensionality in v, α.compContinuousLinearMap L = (λ^{-1})^n • α. Hence ω'(y) = (λ^{-1})^n • ω(λ^{-1} • y) for every y ∈ ℝ^P.

6. By steps 3–5, ω' ∈ TestFormOn univ n satisfies ω'(y) = (λ^{-1})^n • ω(λ^{-1} • y) for all y and C(ω') = C(ω), which is the claim.

## Key steps

1. IsConeCurrent gives currentEval (blowUp C 0 λ) ω = C ω.
2. dilation 0 λ '' univ = univ, so currentEval takes its test-form branch.
3. Unfolding blowUp (affinePushforward of restrictDomain) gives C ω' for the test form ω' = affinePullbackForm (λ^{-1}·id) (−λ^{-1}·0) ω.
4. Multilinearity: α ∘ (λ^{-1}·id) = λ^{-n}α, so ω'(y) = λ^{-n}ω(λ^{-1}y).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp ... GMT/Ch07/Submission.lean (both identical); git -C .lake/packages/{simongmt,mathlib} log -1 (2b3663083f3fe399b6296fb8eaee52169170e197, 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cat -n GMT/Ch07/Contract.lean (IMRep, IMRep.action/Represents/measure, currentEval, dilationCLM, dilation, blowUp, IsConeCurrent)`
- `cat -n simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean (affinePullbackForm, affinePullbackTestOn_coe, GeometricCurrentOn.affinePushforward_apply)`
- `grep -rn restrictDomain simongmt/Poincare/SimonGMT; cat -n Chapter06/CurrentLocalEquality.lean (restrictDomain_apply, testFormOnInclusion_coe)`
- `sed -n 1,200p Chapter06/Currents.lean; sed -n 1,80p Chapter06/Forms.lean (TestFormOn, GeometricCurrentOn, Covector, DifferentialForm, IsTestForm)`
- `sed -n 1,200p Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt)`
- `rg -n HasApproximateTangentSpaceAt simongmt | grep -iE 'smul|dilat|scale|homothet|preimage|image'; rg -n 'theorem .*(smul|dilat|homothet|rescale)' Chapter03 Chapter04 Chapter06; grep '^theorem' Chapter08/TangentRescaling.lean`
- `grep -rn 'hausdorffMeasure_smul\|euclideanHausdorffMeasure_smul\|euclideanHausdorffMeasure_homothety\|map_euclideanHausdorffMeasure\|euclideanHausdorffMeasure_image' mathlib/Mathlib; sed -n 100,180p Mathlib/Geometry/Euclidean/Volume/Measure.lean; sed -n 745,770p Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'theorem map_smul_univ' mathlib/Mathlib; sed -n 510,525p Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `grep -n lipschitzWith_smul Mathlib/Analysis/Normed/MulAction.lean; grep -n 'protected theorem comp' Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `grep -rhoE '"lean_name": *"[^"]+"' nodes dag.json | sort -u; grep -rlE 'euclid_hausdorff_dilation_change_of_variables|approx_tangent_space_smul_preimage|imrep_univ_smul_rescale_exists|cone_current_apply_dilation_pullback|imrep_smul_rescale_action_measure' nodes dag.json problem.json GMT (no match)`
- `sed -n 694,700p book/chapter-07.txt; sed -n 404,410p book/chapter-06.txt; grep -n '1.4 Definition' book/chapter-03.txt`
- `lake env lean /tmp/cmh-decomp/{Stmts,ChildA,ChildB,ChildE,ChildF,ChildD,Final,Inst}.lean (#print axioms; pp.explicit instance check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/TangentRescaling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/MulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/cmh-decomp/Final.lean`
- `/tmp/cmh-decomp/Inst.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean, and the installed simongmt (2b366308) and mathlib (25730c7c) match the pins. SimonGMT supplies the pieces the children need: affinePullbackForm, affinePullbackTestOn_coe and affinePushforward_apply (AffineCurrentPushforward.lean); restrictDomain_apply and testFormOnInclusion_coe (CurrentLocalEquality.lean); CountablyRectifiable, blowUpMap and HasApproximateTangentSpaceAt (Rectifiable.lean, Simon 3.1.1 and 3.1.4). It has no dilation-invariance lemma for HasApproximateTangentSpaceAt or for triples: Chapter08/TangentRescaling.lean treats Chapter 8 general varifolds only. Snapshot Mathlib supplies Measure.euclideanHausdorffMeasure_smul₀ (Geometry/Euclidean/Volume/Measure.lean:152), ContinuousAlternatingMap.map_smul_univ (Topology/Algebra/Module/Alternating/Basic.lean:518), lipschitzWith_smul (Analysis/Normed/MulAction.lean:51) and the measurable-embedding API (restrict_map, lintegral_map, integral_map, ae_map_iff, measurableSet_image). All five child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract's opens. Each is proved in scratch using only propext, Classical.choice and Quot.sound. The parent's exact frozen type follows from them plus the sibling imrep_measure_eq_of_represents_same_current; the only sorryAx is that sibling stub. None of the five proposed names occurs in the DAG. Book lines cited by the proofs were checked: chapter-07.txt 697–698, chapter-06.txt 408, chapter-03.txt 77. No network sources were needed.
