# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.image_imrep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 4 and 5 of the parent proof, which follow Simon Ch. 6, 3.6–3.9 for injective f (chapter-06.txt lines 815–862: f_#T = τ(f(M), θ∘f^{-1}, induced orientation)). Here the orientation is already transported to the source side as the hypothesis on η.
Notation: E := ℝ^P, H^n := μHE[n], M := R.carrier, θ := R.mult, μ := H^n⌞M, M' := φ(M), ν := H^n⌞M'.
1. The inverse. Because φ is bijective it has a two-sided inverse ψ : E → E, with ψ(φ(x)) = x and φ(ψ(y)) = y for all x, y (for example ψ = Function.invFun φ). ψ is Λ-Lipschitz: given y, y', put x = ψ(y) and x' = ψ(y'); the antilipschitz bound gives |ψ(y) − ψ(y')| = |x − x'| ≤ Λ|φ(x) − φ(x')| = Λ|y − y'| (AntilipschitzWith.to_rightInverse). Hence ψ is continuous and Borel measurable. For all S, T ⊆ E:
- φ(S) = ψ^{-1}(S) and ψ(S) = φ^{-1}(S) (Set.image_eq_preimage_of_inverse);
- φ(S) ∩ T = φ(S ∩ φ^{-1}(T)) (Set.image_inter_preimage).
2. Lipschitz images. Since φ is Λ-Lipschitz, H^n(φ(A)) ≤ Λ^n H^n(A) for every A ⊆ E. This is Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn; equivalently, Mathlib's LipschitzWith.hausdorffMeasure_image_le with d = n, since μHE[n] is a constant multiple of μH[n].
3. Image-measure comparison. For every S ⊆ E, ψ_#(H^n⌞φ(S)) ≤ Λ^n·(H^n⌞S) as measures.
It suffices to compare values on Borel sets A (Measure.le_iff). Since ψ is measurable, ψ^{-1}(A) is Borel and ψ_#(H^n⌞φ(S))(A) = H^n(ψ^{-1}(A) ∩ φ(S)).
Moreover ψ^{-1}(A) ∩ φ(S) = φ(A ∩ S). If y = φ(x) with x ∈ S and ψ(y) ∈ A, then x = ψ(φ(x)) = ψ(y) ∈ A, so y ∈ φ(A ∩ S). Conversely, if y = φ(x) with x ∈ A ∩ S, then ψ(y) = x ∈ A and y ∈ φ(S).
By step 2, ψ_#(H^n⌞φ(S))(A) = H^n(φ(A ∩ S)) ≤ Λ^n H^n(A ∩ S) = Λ^n (H^n⌞S)(A).
With S = M this gives ψ_#ν ≤ Λ^n μ. Consequently, if N is a Borel μ-null set, then ν(ψ^{-1}(N)) = (ψ_#ν)(N) ≤ Λ^n μ(N) = 0. So ψ is quasi-measure-preserving from ν to μ (ψ_#ν ≪ μ by Measure.absolutelyContinuous_of_le_smul).
4. Definition. Let R' := (M', θ', ξ') with θ'(y) := θ(ψ(y)) and ξ'(y) := η(ψ(y)).
5. The fields of IMRep U n.
(a) M' = ψ^{-1}(M) is Borel, since M is Borel (R.measurableSet_carrier) and ψ is measurable.
(b) M' ⊆ U: if x ∈ M, then x ∈ U = φ^{-1}(U) (R.carrier_subset), so φ(x) ∈ U.
(c) M' is countably n-rectifiable. By R.rectifiable there are a set M₀ with H^n(M₀) = 0 and Lipschitz maps F_j : ℝ^n → E (j ∈ ℕ, with constants K_j) such that M ⊆ M₀ ∪ ⋃_j F_j(ℝ^n). Then:
- H^n(φ(M₀)) ≤ Λ^n·0 = 0 by step 2;
- φ∘F_j is (Λ·K_j)-Lipschitz;
- M' ⊆ φ(M₀) ∪ ⋃_j (φ∘F_j)(ℝ^n), because for y = φ(x) with x ∈ M, either x ∈ M₀ and y ∈ φ(M₀), or x = F_j(v) and y = (φ∘F_j)(v).
(d) θ' = θ∘ψ is measurable, since θ : E → ℕ and ψ are measurable.
(e) If y ∈ M', then y = φ(x) with x ∈ M, and θ'(y) = θ(ψ(φ(x))) = θ(x) > 0 by R.mult_pos.
(f) Local integrability. Let K ⊆ U be compact and K' := φ^{-1}(K). Then K' = ψ(K) is compact (continuous image of a compact set), K' ⊆ φ^{-1}(U) = U, and M' ∩ K = φ(M ∩ K') by step 1.
Put ρ := H^n⌞φ(M ∩ K'). Since θ (as a [0, ∞]-valued function) and ψ are measurable, the change of variables for image measures (lintegral_map) gives ∫⁻_{M'∩K} θ' dH^n = ∫⁻ θ∘ψ dρ = ∫⁻ θ d(ψ_#ρ).
By step 3 with S = M ∩ K', ψ_#ρ ≤ Λ^n·H^n⌞(M ∩ K'). By monotonicity of the integral in the measure, ∫⁻ θ d(ψ_#ρ) ≤ Λ^n ∫⁻_{M∩K'} θ dH^n.
The right side is finite: Λ^n < ∞, and ∫⁻_{M∩K'} θ dH^n < ∞ by R.locallyIntegrable_mult applied to the compact K' ⊆ U.
(The parent proof gets this bound from the area formula and J ≤ Λ^n. The comparison of step 3, which the parent uses in 5(g), gives it without the Jacobian.)
(g) ξ' is ν-a.e. strongly measurable. By hypothesis η is μ-a.e. strongly measurable, so η = η̃ outside a Borel μ-null set N, for some strongly measurable η̃. Then η̃∘ψ is strongly measurable (ψ is measurable), and η∘ψ = η̃∘ψ outside ψ^{-1}(N), which is ν-null by step 3. Hence ξ' = η∘ψ is ν-a.e. strongly measurable (AEStronglyMeasurable.comp_quasiMeasurePreserving).
(h) Orientation. Let p(x) be the statement: there is a subspace Q with HasApproximateTangentSpaceAt n M' (φ(x)) Q and IsUnitOrientationOf (η(x)) Q. By hypothesis p(x) holds outside a μ-null set, hence outside a Borel μ-null set N. By step 3, ψ^{-1}(N) is ν-null, so p(ψ(y)) holds for ν-a.e. y (QuasiMeasurePreserving.ae). For such y, φ(ψ(y)) = y and η(ψ(y)) = ξ'(y), so there is Q with HasApproximateTangentSpaceAt n M' y Q and IsUnitOrientationOf (ξ'(y)) Q. This is the orients field of R'.
6. Conclusion. R' is an IMRep U n with R'.carrier = φ(M) = φ '' R.carrier. For every x ∈ E:
- R'.mult(φ(x)) = θ(ψ(φ(x))) = θ(x) = R.mult x;
- R'.orient(φ(x)) = η(ψ(φ(x))) = η(x).

## Key steps

1. The two-sided inverse ψ of φ is Λ-Lipschitz (antilipschitz), hence continuous and measurable; φ(S) = ψ^{-1}(S), ψ(S) = φ^{-1}(S) and φ(S) ∩ T = φ(S ∩ φ^{-1}(T)).
2. H^n(φ(A)) ≤ Λ^n H^n(A). Since ψ^{-1}(A) ∩ φ(S) = φ(A ∩ S), we get ψ_#(H^n⌞φ(S)) ≤ Λ^n H^n⌞S, so ψ is quasi-measure-preserving from H^n⌞φ(M) to H^n⌞M.
3. Define R' = (φ(M), θ∘ψ, η∘ψ). The carrier is Borel (= ψ^{-1}(M)), lies in U (φ^{-1}(U) = U), and is rectifiable (φ(M₀) is null and φ∘F_j is Lipschitz); θ∘ψ is measurable and positive on φ(M).
4. Local integrability: ∫⁻_{φ(M)∩K} θ∘ψ dH^n = ∫⁻ θ d(ψ_#H^n⌞φ(M∩φ^{-1}K)) ≤ Λ^n ∫⁻_{M∩φ^{-1}K} θ dH^n < ∞, with φ^{-1}K = ψ(K) compact and contained in U.
5. A.e. strong measurability and a.e. orientation of η∘ψ transfer from μ to ν by quasi-measure-preservation. φ∘ψ = id gives the orients field, and ψ∘φ = id gives R'.mult∘φ = θ and R'.orient∘φ = η.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-89b1ce4202/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `python3 -I: nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-v{1,2,3}.json sibling keys, lean_names and frozen lean_statements`
- `python3 -I: dag.json status of the 12 diffeo_pushforward nodes; regex scan of all 509 lean_names for integrab|change_of_var|imrep|lipschitz|hausdorff|quasi|pushforward|image`
- `grep -rl '"dpfir_bilipschitz_image_imrep_exists"|"dpfir_imrep_pairing_continuous_integrable"|"dpfir_integral_eq_of_area_lintegral"' dag.json nodes/*/decomposition-v*.json (no hits)`
- `rg -n 'μHE\[|def euclideanHausdorffMeasure' mathlib/Mathlib; rg -n hausdorffMeasure_image_le mathlib/Mathlib`
- `rg -n 'theorem to_rightInverse|absolutelyContinuous_of_le_smul|comp_quasiMeasurePreserving|integral_eq_lintegral_pos_part_sub_lintegral_neg_part|def compContinuousLinearMapCLM|continuous_compContinuousLinearMapCLM|bounded_above_of_compact_support|image_eq_preimage_of_inverse|enorm_eq_ofReal' mathlib/Mathlib`
- `rg -n 'theorem ContDiff.continuous_fderiv|clm_comp|clm_apply|apply_continuousLinearMap|comp_aestronglyMeasurable₂|zero_compContinuousLinearMap' mathlib/Mathlib`
- `rg -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03; rg -n 'abbrev Covector|abbrev DifferentialForm|def IsTestForm|testFormOnSubmodule' simongmt/Poincare/SimonGMT/Chapter06`
- `rg -n 'euclideanHausdorffMeasure_image_le_of_lipschitzOn|weighted_area_formula|QuasiMeasurePreserving' simongmt/Poincare/SimonGMT`
- `rg -n 'Integrable|bilipschitz|QuasiMeasurePreserving|image.*IMRep' project/GMT --glob '*.lean'; rg -n dpfir_ project mathlib (no match)`
- `git show <solution ref of rsd_mw_wlm_integrable_clm_comp>:GMT/Ch07/Submission.lean (handling of MultiVector topology)`
- `python3 -I: gmt-compare.py contract_scope(GMT/Ch07/Contract.lean, GMT.Ch07.main_theorem)`
- `sed -n 420,445p and 810,865p book/chapter-06.txt (Simon 6.2.24(3), 6.3.6–3.9)`
- `lake env lean /tmp/dpfir-scratch/Types.lean (child types elaborate)`
- `lake env lean /tmp/dpfir-scratch/Inst.lean, Inst2.lean, Comp.lean (#synth PseudoMetrizableSpace probes; ζ measurability idiom)`
- `lake env lean /tmp/dpfir-scratch/AssemblyCond3.lean (#print axioms assembly_conditional3)`
- `lake env lean /tmp/dpfir-scratch/Final.lean (#print axioms TestC2, TestA, TestB, assembly_conditional3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-89b1ce4202/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-89b1ce4202/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dpfir-scratch/Types.lean`
- `/tmp/dpfir-scratch/AssemblyCond3.lean`
- `/tmp/dpfir-scratch/ChildC2.lean`
- `/tmp/dpfir-scratch/ChildA.lean`
- `/tmp/dpfir-scratch/ChildB.lean`
- `/tmp/dpfir-scratch/Final.lean`
- `/tmp/dpfir-scratch/Comp.lean`

The local snapshot proves neither this statement nor any of the three children. The project GMT tree has no bi-Lipschitz IMRep image lemma, no pairing-integrability lemma for continuous covector fields, and no area-to-Bochner transfer, and no dpfir_ name occurs anywhere. The accepted DAG lemmas regcomp_rim_action_integrable and rsd_cmr_ic_action_integrable cover only test forms ω ∈ TestFormOn U n, so pairing_integrable is a new generalization.

Every library fact the child proofs use exists at the pinned revisions:
- Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, importable from GMT.Ch07.Submission;
- LipschitzWith.hausdorffMeasure_image_le and AntilipschitzWith.to_rightInverse;
- Measure.absolutelyContinuous_of_le_smul and AEStronglyMeasurable.comp_quasiMeasurePreserving;
- integral_eq_lintegral_pos_part_sub_lintegral_neg_part;
- ContinuousAlternatingMap.le_opNorm and continuous_compContinuousLinearMapCLM;
- Continuous.bounded_above_of_compact_support and Set.image_eq_preimage_of_inverse.

The definitions of CountablyRectifiable (null M₀ plus Lipschitz F_j : ℝ^n → E) and HasApproximateTangentSpaceAt (with its uniqueness lemma) match the child proofs.

Typeclass pitfall: PseudoMetrizableSpace cannot be synthesized for MultiVector P n or for Covector →L Covector. Measurability of ζ in the parent therefore goes through continuous_fst.clm_comp continuous_snd composed with prodMk and id, which compiles.

In Lean, the three child types elaborate in the comparator's replayed scope. A conditional proof of the exact frozen parent type from the four frozen sibling types plus the three child types compiles using only propext, Classical.choice and Quot.sound, and complete proofs of all three children compile with the same axioms.
