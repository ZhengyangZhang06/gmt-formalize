# Parent-supplied natural-language proof

- Parent DAG node: `root.variation_formulas-a1.image_area_formula-a1`
- Child DAG node: `root.variation_formulas-a1.image_area_formula-a1.chart_image_area-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5–8 of the parent proof, for one chart and one Borel set B. Mathematically, this is the one-chart case of the area formula for f on M stated after Simon Ch. 2, 4.12. It is obtained from the area formula 3.2/3.5 applied in a chart and the Jacobian chain rule 4.11. M is an arbitrary set here: only the single local representation (V, W, ψ) is used. The chart area formulas are the axiom-clean SimonGMT lemmas in Poincare.SimonGMT.Chapter02.WeightedArea. The frozen contract imports only Chapter02.Submanifold (which re-exports Chapter02.Area), so the Submission must add `import Poincare.SimonGMT.Chapter02.WeightedArea`.

Notation.
- J(y) := areaJacobian(Df(y) ∘ ι_y) for y ∈ ℝᴺ, where ι_y = (tangentSpace M y).subtypeL.
- B′ := V ∩ ψ⁻¹(B) ⊆ ℝⁿ, and F := f ∘ ψ.
- For a map G between Euclidean spaces, SimonGMT defines areaJacobianAt G x := normDet(DG(x)). SimonGMT areaJacobianAt_eq_sqrt_det_adjoint_comp gives areaJacobianAt G x = √det(DG(x)* ∘ DG(x)), which is literally areaJacobian(DG(x)) for the contract's definition.
- finrank ℝ ℝⁿ = n (finrank_euclideanSpace_fin). So the SimonGMT statements written with μHE[finrank ℝ ℝⁿ] are statements about μHE[n].

1. Chart facts. IsSimonLocalRepresentation 1 M V W ψ gives:
   - V is open;
   - ψ is C¹ on V and injective on V;
   - ψ(V) = W ∩ M;
   - Dψ(x) is injective for every x ∈ V.
   V is open and ψ is C¹ (order 1 ≠ 0) on V. So ψ is differentiable at every x ∈ V (ContDiffOn.differentiableOn, then DifferentiableOn.differentiableAt using V ∈ 𝓝 x), and ψ is continuous on V.
2. B′ is Borel and B′ ⊆ V.
   - The restriction of ψ to the subtype V is continuous (continuousOn_iff_continuous_domRestrict), hence measurable.
   - So the preimage of the Borel set B under this restriction is a measurable subset of the subtype V.
   - V is open, hence measurable, so Subtype.val : V → ℝⁿ is a measurable embedding (MeasurableEmbedding.subtype_coe).
   - Therefore the image of that preimage under Subtype.val is Borel, and this image is exactly V ∩ ψ⁻¹(B) = B′.
   - Clearly B′ ⊆ V.
3. ψ(B′) = B. If x ∈ B′, then ψ(x) ∈ B. Conversely, let y ∈ B. Then y ∈ W ∩ M = ψ(V), so y = ψ(x) for some x ∈ V, and that x lies in B′.
4. F on B′. Let x ∈ B′, so x ∈ V and ψ(x) ∈ B.
   - By 1, ψ is differentiable at x, and f is differentiable at ψ(x) by hypothesis. So F is differentiable at x, with DF(x) = Df(ψ x) ∘ Dψ(x) (chain rule, fderiv_comp).
   - DF(x) is injective: it is the composition of Dψ(x), injective by 1, and Df(ψ x), injective by hypothesis since ψ x ∈ B.
   - F is injective on B′. Let x, x′ ∈ B′ with f(ψ x) = f(ψ x′). Then ψ x, ψ x′ ∈ B, and injectivity of f on B gives ψ x = ψ x′. Injectivity of ψ on V ⊇ B′ then gives x = x′.
5. Unweighted area formula. Apply SimonGMT injective_area_formula_areaJacobianAt with E = ℝⁿ, F = ℝ^{N′}, s = B′; its hypotheses hold by 2 and 4. It gives
   μHE[n](F(B′)) = ∫⁻_{x∈B′} ofReal(areaJacobianAt F x) dμHE[n](x).
   Since F(B′) = f(ψ(B′)) = f(B) (Set.image_comp and 3), this reads
   μHE[n](f(B)) = ∫⁻_{x∈B′} ofReal(areaJacobianAt F x) dμHE[n](x).
6. Jacobian factorization. Let x ∈ B′ and y := ψ(x).
   - By the notation and 4: areaJacobianAt F x = areaJacobian(Df(y) ∘ Dψ(x)), and areaJacobianAt ψ x = areaJacobian(Dψ(x)).
   - Since x ∈ V, the hypothesis gives tangentSpace M y = range Dψ(x).
   - The sibling lemma variation_areaJacobian_chain_rule, with L = Dψ(x), A = Df(y) and T = tangentSpace M y, gives
     areaJacobian(Df(y) ∘ Dψ(x)) = areaJacobian(Df(y) ∘ ι_y) · areaJacobian(Dψ(x)),
     that is, areaJacobianAt F x = J(y) · areaJacobianAt ψ x.
   - Both factors are square roots, hence ≥ 0. So ENNReal.ofReal_mul gives
     ofReal(areaJacobianAt F x) = ofReal(areaJacobianAt ψ x) · ofReal(J(ψ x)).
   This holds for every x in the measurable set B′, so setLIntegral_congr_fun turns 5 into
   μHE[n](f(B)) = ∫⁻_{x∈B′} ofReal(areaJacobianAt ψ x) · ofReal(J(ψ x)) dμHE[n](x).
7. Weighted chart formula. Apply SimonGMT IsSimonLocalRepresentation.weighted_area_formula with:
   - r = 1 (so 1 ≤ r holds);
   - the Borel set s = B′ ⊆ V (step 2);
   - the weight g := ofReal ∘ J : ℝᴺ → [0,∞]. This lemma requires no measurability of g.
   It gives
   ∫⁻_{y∈ψ(B′)} ofReal(J(y)) dμHE[n](y) = ∫⁻_{x∈B′} ofReal(areaJacobianAt ψ x) · ofReal(J(ψ x)) dμHE[n](x).
   By 3, the left side is ∫⁻_{y∈B} ofReal(J(y)) dμHE[n](y).
8. Combining 6 and 7:
   μHE[n](f(B)) = ∫⁻_{y∈B} ofReal(areaJacobian(Df(y) ∘ ι_y)) dμHE[n](y). ∎

Implementation notes (Lean, pinned toolchain).
- Use continuousOn_iff_continuous_domRestrict and Set.domRestrict; the older names continuousOn_iff_continuous_restrict and Set.restrict are deprecated.
- ContinuousLinearMap.coe_comp is the function-coercion lemma ⇑(A ∘L L) = ⇑A ∘ ⇑L.
- For ENNReal.ofReal_mul, prove 0 ≤ areaJacobian K from Real.sqrt_nonneg after unfolding areaJacobian.
- Give auxiliary lemmas a node-specific prefix (e.g. variation_chart_image_area_aux…) so that merged Submission files cannot clash.

## Key steps

1. Chart facts: V is open, ψ is C¹ and hence differentiable and continuous on V, InjOn ψ V, ψ(V) = W ∩ M, and Dψ(x) is injective on V.
2. B′ := V ∩ ψ⁻¹(B) is Borel (continuous restriction of ψ to the open subtype V, then MeasurableEmbedding.subtype_coe), B′ ⊆ V, and ψ(B′) = B.
3. F = f ∘ ψ is differentiable on B′ with injective derivative Df(ψ x) ∘ Dψ(x) (fderiv_comp), and F is injective on B′.
4. SimonGMT injective_area_formula_areaJacobianAt plus F(B′) = f(B): μHE[n](f(B)) = ∫⁻_{B′} ofReal(areaJacobianAt F).
5. Sibling variation_areaJacobian_chain_rule with T = tangentSpace M (ψ x) = range Dψ(x) gives areaJacobianAt F x = J(ψ x) · areaJacobianAt ψ x; split ofReal of the product of nonnegative reals.
6. SimonGMT IsSimonLocalRepresentation.weighted_area_formula (r = 1, s = B′, weight ofReal ∘ J), with ψ(B′) = B, turns the integral into ∫⁻_B ofReal(J) dμHE[n].

## Reference use

### local-project

Queries:
- `rg -n '^theorem|^lemma|^noncomputable def|^def' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean; sed -n 40,80p and 260,372p NormDet.lean (normDet, normDet_nonneg, ContinuousLinearMap.normDet_sq, normDet_comp)`
- `rg -n -A4 'theorem setLIntegral_congr_fun |theorem MeasurableSet.image_of_continuousOn_injOn|theorem lintegral_iUnion |theorem measure_iUnion |theorem IsLindelof.indexed_countable_subcover' mathlib/Mathlib`
- `rg -n 'HereditarilyLindelofSpace.isLindelof|theorem isOpen_iUnion_countable|theorem disjoint_disjointed|theorem disjointed_subset|theorem iUnion_disjointed|theorem MeasurableSet.disjointed|theorem finrank_euclideanSpace_fin|theorem fderiv_comp ' mathlib/Mathlib`
- `rg -n 'continuousOn_iff_continuous_restrict|MeasurableEmbedding.subtype_coe|measurableSet_image|InjOn.image_inter|disjoint_image_iff' mathlib/Mathlib`
- `rg -n 'μHE\[' mathlib/Mathlib (euclideanHausdorffMeasure notation)`
- `rg -n 'injective_area_formula|weighted_area_formula|areaJacobian' mathlib/Mathlib (no match)`
- `rg -n 'areaJacobian|subtypeL' project/GMT/Ch02/Contract.lean; cmp project/GMT/Ch02/{Contract,Submission}.lean against the workspace copies (identical)`
- `cat simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,WeightedArea,Area}.lean; sed -n 230,320p SubmanifoldCalculus.lean; cat AreaSubmanifoldExample.lean`
- `grep -rn 'isOpen_iUnion_countable|countable_cover|atlas' simongmt/Poincare --include=*.lean`
- `grep -n '4.11|4.12|Jacobian' book/sources/chapter-02-source.txt; sed -n 740,1000p (Simon 3.1–3.6, 4.1–4.13)`
- `cat verifier/lean_contract.py; sed -n 330,384p and 425,600p verifier/gmt-compare.py (candidate_inputs, child_contract, contract_scope, child_modules)`
- `python3 -I scripts/gen_checks.py (verifier child_modules/contract_scope + validate_lean_statement) then lean checks/NodeChallenge_0{0,1,2}_*.lean against scratch olean of frozen GMT.Ch02.Submission (lean -o, LEAN_PATH = lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `lean checks/FullProof.lean; lean checks/StandInAssembly.lean; lean checks/StandInChart.lean; lean checks/NoImport_Child1.lean; lean checks/NoImport_StandInAssembly.lean; lean checks/InstCheck.lean`
- `lean -o candout/GMT/Ch02/Submission.olean cand/GMT/Ch02/Submission.lean; lean checks/AxSolution_0{0,1,2}_*.lean (generated exact Submission.X modules + #print axioms)`
- `python3 -I scan of dag.json lean_name fields and nodes/*/decomposition-v*.json subproblem lean_names; git show <branch>:GMT/Ch02/Submission.lean | grep over all branches (collision check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/Lindelof.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaSubmanifoldExample.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-image-area-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-image-area-formula-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-borel-coarea-a1/decomposition-v1.json`
- `/tmp/imgarea-decomp-bwpafg/scripts/gen_checks.py`
- `/tmp/imgarea-decomp-bwpafg/scripts/statements.json`
- `/tmp/imgarea-decomp-bwpafg/checks/NodeChallenge_00_variation_areaJacobian_chain_rule.lean`
- `/tmp/imgarea-decomp-bwpafg/checks/NodeChallenge_01_variation_chart_image_area.lean`
- `/tmp/imgarea-decomp-bwpafg/checks/NodeChallenge_02_variation_submanifold_image_area.lean`
- `/tmp/imgarea-decomp-bwpafg/checks/FullProof.lean`
- `/tmp/imgarea-decomp-bwpafg/checks/StandInAssembly.lean`
- `/tmp/imgarea-decomp-bwpafg/checks/StandInChart.lean`
- `/tmp/imgarea-decomp-bwpafg/checks/InstCheck.lean`
- `/tmp/imgarea-decomp-bwpafg/checks/AxSolution_00_variation_areaJacobian_chain_rule.lean`
- `/tmp/imgarea-decomp-bwpafg/cand/GMT/Ch02/Submission.lean`

Pinned Mathlib (25730c7c) has no area formula on submanifolds and no `areaJacobian` (rg: no match). Its NormDet.lean supplies everything the 4.11 child needs: LinearMap.normDet_comp (unconditional, finite-dimensional source), ContinuousLinearMap.normDet_sq and LinearMap.normDet_nonneg. SimonGMT (2b36630) provides the chart tools for child 2: injective_area_formula_areaJacobianAt and IsSimonLocalRepresentation.weighted_area_formula (WeightedArea.lean; the weight need not be measurable), and areaJacobianAt_eq_sqrt_det_adjoint_comp (Area.lean), which identifies areaJacobianAt with the contract's areaJacobian of fderiv. WeightedArea is not imported by the frozen contract, so only the chart child must add that import; the verifier permits extra imports in the Submission. SimonGMT's IsSimonSubmanifold.nonempty_volumeAtlas (AreaSubmanifoldExample.lean) shows the Lindelöf atlas is a few lines, so the gluing stays in the parent. The book (lines 740–1000) confirms the structure: 3.6(2) decomposes a Borel set into chart pieces, 4.11 gives J_{f∘ψ} = J_ψ·J^M_f, and the passage after 4.12 states the area formula for f on M. Lean: both child statements elaborate in contract scope with canonical Submodule instances. Full proofs of both children and of the parent's exact frozen type compile with axioms [propext, Classical.choice, Quot.sound]; the parent also compiles from sorried stand-ins of the children. The generated `exact Submission.X` solution modules compile against a candidate Submission with the same axioms. Neither proposed name collides with any reserved name.
