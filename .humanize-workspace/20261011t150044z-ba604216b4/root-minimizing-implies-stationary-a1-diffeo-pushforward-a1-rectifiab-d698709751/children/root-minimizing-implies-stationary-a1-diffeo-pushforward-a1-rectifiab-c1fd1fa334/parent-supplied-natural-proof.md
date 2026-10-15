# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.rectifiable_area_formula-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.rectifiable_area_formula-a1.piece_area-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 5 of the parent proof (dpf_area_formula_bilipschitz_rectifiable; Simon Ch. 3, 2.3–2.6, J^M_f = sqrt(det(D_{τ_p}f · D_{τ_q}f)) for an orthonormal basis τ of T_xM), for a single piece, with the tangent field abstracted to Q and details filled in.
Notation:
- E := ℝ^P, H^n := μHE[n], λ := volume (Lebesgue measure) on ℝ^n = Euclid n.
- For a linear map T between finite-dimensional real inner product spaces, normDet(T) ≥ 0 is Mathlib's LinearMap.normDet (the square root of det(T*T)).
- For f : ℝ^n → E, areaJacobianAt f a = normDet(Df(a)) (SimonGMT areaJacobianAt_eq_normDet), where Df(a) := fderiv ℝ f a, which is 0 where f is not differentiable.
- For a linear T : E → E and a subspace V, T|_V := (T : E →ₗ E).domRestrict V.
- J(x) := sqrt(det(⟨Dφ(x)e^x_a, Dφ(x)e^x_b⟩)_{a,b}) with e^x := stdOrthonormalBasis ℝ (Q x).
1. Area formula used. SimonGMT Chapter02 weighted_area_formula_lipschitz_injOn states: if f : ℝ^n → E is K-Lipschitz, s ⊆ ℝ^n is Borel, f is injective on s, and w : E → [0, ∞] is arbitrary, then ∫⁻_{f(s)} w dμHE[finrank ℝ ℝ^n] = ∫⁻_s ofReal(areaJacobianAt f a) · w(f(a)) dλ(a). Since finrank ℝ ℝ^n = n (finrank_euclideanSpace_fin), the measure on the left is H^n.
2. Gram identity. Let T : E → E be continuous linear, V a subspace of E, and e := stdOrthonormalBasis ℝ V (indexed by Fin (finrank ℝ V)). Then normDet(T|_V) = sqrt(det(⟨T e_a, T e_b⟩)_{a,b}).
 Proof: Mathlib LinearMap.normDet_sq_eq_det_gram, applied to f := T|_V and the orthonormal basis e of V, gives normDet(f)^2 = det(Matrix.gram ℝ (a ↦ f(e_a))). Here f(e_a) = T(e_a), and Matrix.gram ℝ v = Matrix.of (a, b ↦ ⟨v_a, v_b⟩), with the coercion ℝ → ℝ being the identity. So normDet(f)^2 = det(⟨T e_a, T e_b⟩)_{a,b}. Since normDet(f) ≥ 0 (LinearMap.normDet_nonneg), normDet(f) = sqrt(normDet(f)^2) = sqrt(det(⟨T e_a, T e_b⟩)_{a,b}).
 Consequence: if V' and W are subspaces with V' = W, then sqrt(det(⟨T e'_a, T e'_b⟩)_{a,b}) with e' := stdOrthonormalBasis ℝ V' equals normDet(T|_W). Substitute V' = W and apply the identity. In Lean, state this for an arbitrary V' and close it with `rintro V' rfl`; rewriting the equation directly under normDet fails because of the dependent FiniteDimensional instance.
3. The composite. Φ := φ ∘ F is (ΛL)-Lipschitz (LipschitzWith.comp). Φ is injective on B, because F is injective on B, F maps B into F(B), and φ is injective on F(B) (Set.InjOn.comp with mapsTo_image). Also φ(F(B)) = Φ(B) (Set.image_comp).
4. Left side. Apply 1 to f := Φ, s := B, w := g: ∫⁻_{φ(F(B))} g dH^n = ∫⁻_{Φ(B)} g dH^n = ∫⁻_B ofReal(areaJacobianAt Φ b) · g(Φ(b)) dλ(b).
5. Right side. Apply 1 to f := F, s := B and the weight w(x) := ofReal(J(x)) · g(φ(x)), which is arbitrary (no measurability is needed): ∫⁻_{F(B)} ofReal(J(x)) · g(φ(x)) dH^n(x) = ∫⁻_B ofReal(areaJacobianAt F b) · (ofReal(J(F(b))) · g(φ(F(b)))) dλ(b).
6. The integrands of 4 and 5 agree for λ⌞B-a.e. b.
 By Rademacher's theorem (Mathlib LipschitzWith.ae_differentiableAt with the Haar measure λ), the Lipschitz map F is differentiable at λ-a.e. point, hence λ⌞B-a.e. (ae_restrict_of_ae). By hypothesis, Q(F(b)) = range DF(b) for λ⌞B-a.e. b. Fix b with both properties.
 Since φ is differentiable at F(b), the chain rule (fderiv_comp) gives DΦ(b) = Dφ(F(b)) ∘ DF(b). Viewing these as linear maps (ContinuousLinearMap.toLinearMap_comp), Mathlib LinearMap.normDet_comp gives normDet(DΦ(b)) = normDet(Dφ(F(b))|_{range DF(b)}) · normDet(DF(b)).
 By the consequence in 2, with T := Dφ(F(b)), V' := Q(F(b)) and W := range DF(b), we get J(F(b)) = normDet(Dφ(F(b))|_{range DF(b)}). Hence areaJacobianAt Φ b = J(F(b)) · areaJacobianAt F b.
 Since J(F(b)) is a square root and hence ≥ 0, ENNReal.ofReal_mul gives ofReal(areaJacobianAt Φ b) = ofReal(J(F(b))) · ofReal(areaJacobianAt F b). Using Φ(b) = φ(F(b)) and commutativity and associativity of multiplication in [0, ∞], ofReal(areaJacobianAt Φ b) · g(Φ(b)) = ofReal(areaJacobianAt F b) · (ofReal(J(F(b))) · g(φ(F(b)))).
7. Conclusion. By 6 and lintegral_congr_ae for the measure λ⌞B, the right sides of 4 and 5 are equal. Hence ∫⁻_{φ(F(B))} g dH^n = ∫⁻_{F(B)} ofReal(J(x)) · g(φ(x)) dH^n(x), which is the claim. The argument works for every n ≥ 0. Imports: the Lean proof needs Mathlib.Analysis.InnerProductSpace.NormDet and Poincare.SimonGMT.Chapter02.AreaLipschitz, which the submission may import; the statement itself needs neither.

## Key steps

1. The weighted injective Lipschitz area formula, with finrank ℝ ℝ^n = n, converts H^n-integrals over f(B) into λ-integrals over B with weight ofReal(normDet Df) and an arbitrary w.
2. Gram identity: normDet(T|_V) = sqrt det(⟨T e_a, T e_b⟩) for e = stdOrthonormalBasis ℝ V, via normDet_sq_eq_det_gram and normDet ≥ 0.
3. Φ = φ∘F is Lipschitz and injective on B, and φ(F(B)) = Φ(B). Apply the area formula to Φ with weight g, and to F with weight ofReal(J)·(g∘φ).
4. For λ⌞B-a.e. b (Rademacher plus the hypothesis on Q): the chain rule and normDet_comp, with range DF(b) = Q(F(b)) and the Gram identity, give normDet(DΦ(b)) = J(F(b))·normDet(DF(b)).
5. ENNReal.ofReal_mul and lintegral_congr_ae equate the two λ-integrals.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c)`
- `diff -q local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical; Submission.lean == Contract.lean)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-d698709751/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}; compare nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-v2.json vs decomposition-v3.json (sibling contracts identical)`
- `python3 -I: dag.json scan of 509 nodes for lean_name collisions with dpf_raf_lintegral_image_eq_tsum_pieces / dpf_raf_piece_area_formula_gram (none) and for lean_statements stating approxTangentPlane equalities or tsums of lintegrals (no reusable lemma)`
- `grep -l dpf_raf nodes/*/*.json (no match)`
- `rg -n 'dpf_raf|piece_area|lintegral_image_eq_tsum|approxTangentPlane_eq|normDet' project/GMT --glob '*.lean' (only Ch03 contract normDet comments/defs; no reusable lemma)`
- `rg -n 'theorem normDet_comp |theorem normDet_sq_eq_det_gram|theorem normDet_nonneg' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n 'theorem lintegral_iUnion |theorem setLIntegral_congr ' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/; rg MeasurableSet.image_of_continuousOn_injOn (Constructions/Polish/Basic.lean), fderiv_comp (FDeriv/Comp.lean), toLinearMap_comp (ContinuousLinearMap/Basic.lean), ae_differentiableAt (Calculus/Rademacher.lean), disjoint_image_iff (Data/Set/Image.lean), ae_eq_set (OuterMeasure/AE.lean)`
- `grep -n in lake-packages-25730c7c/simongmt (2b366308): weighted_area_formula_lipschitz_injOn, areaJacobianAt_eq_normDet, def HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, euclideanHausdorffMeasure_image_le_of_lipschitzOn`
- `python3 -I gmt-compare.py contract_scope(GMT.Ch07.main_theorem) and child_modules(...,'contract') -> /tmp/raf-split-check/gen/{image_split,piece_area}_Challenge.lean; lake env lean on each`
- `lake env lean /tmp/raf-split-check/Avail.lean`
- `lake env lean /tmp/raf-split-check/Types.lean`
- `lake env lean /tmp/raf-split-check/Assembly.lean (#print axioms assembly_conditional)`
- `lake env lean /tmp/raf-split-check/Children.lean (#print axioms proto_image_split, proto_piece_area)`
- `lake env lean /tmp/raf-split-check/EndToEnd.lean (GMT.Ch07.Submission.<name> declarations + exact-solution targets; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-d698709751/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-v3.json`
- `/tmp/raf-split-check/Avail.lean`
- `/tmp/raf-split-check/Types.lean`
- `/tmp/raf-split-check/Assembly.lean`
- `/tmp/raf-split-check/Children.lean`
- `/tmp/raf-split-check/EndToEnd.lean`
- `/tmp/raf-split-check/gen/image_split_Challenge.lean`
- `/tmp/raf-split-check/gen/piece_area_Challenge.lean`

The pinned snapshot proves neither child nor the selected statement; the only related project text is Ch03's normDet-based Jacobian definitions. The snapshot's Ch07 Contract.lean is byte-identical to the workspace Contract and Submission. After `import GMT.Ch07.Submission`, LinearMap.normDet, Matrix.gram, areaJacobianAt and weighted_area_formula_lipschitz_injOn are not in scope (Avail.lean reports unknown identifiers). That is why both child statements avoid normDet and use the Matrix.of Gram form of the frozen parent. The following are in scope: MeasurableSet.image_of_continuousOn_injOn, lintegral_iUnion, setLIntegral_congr, ae_eq_set, LipschitzWith.ae_differentiableAt, SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn, HasApproximateTangentSpaceAt.unique and approxTangentPlane. The pinned Mathlib (NormDet.lean) provides normDet_sq_eq_det_gram, normDet_comp and normDet_nonneg. Pinned SimonGMT (2b366308) provides weighted_area_formula_lipschitz_injOn, which takes an arbitrary weight and has no rank hypothesis, and areaJacobianAt_eq_normDet. Lean verification: both frozen child types and the parent type elaborate in the comparator's own generated challenge modules. The conditional parent assembly from the two children plus the two sibling frozen types compiles with only propext, Classical.choice and Quot.sound. Full prototype proofs of both children compile as GMT.Ch07.Submission.<name> with the extra imports, and `exact Submission.<name>` closes each frozen type, with the same axioms. A Lean check also confirmed that the Matrix.of Gram expression equals normDet of the domain-restricted map. No proposed name collides with the 509 DAG nodes or with stored proposals.
