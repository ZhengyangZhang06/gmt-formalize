# Parent-supplied natural-language proof

- Parent DAG node: `root.c1_sard-a1`
- Child DAG node: `root.c1_sard-a1.jacobian_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof of root.c1_sard-a1, PART II step 3 (J*f is continuous on M because L_x L_x* = Df(x) P_x Df(x)*) and step 5 (relative closedness of the critical part of a fiber, F := closure). Only the stated hypotheses are used; M need not be a submanifold here (continuity of x ↦ P_x on M is assumed; in the parent it comes from the sibling node submanifold_tangent).

Notation. For x ∈ ℝᴺ: T_x := tangentSpace M x, ι_x : T_x → ℝᴺ the inclusion, π_x : ℝᴺ → T_x the orthogonal projection, P_x := tangentProjection M x = (T_x).starProjection = ι_x ∘ π_x, A_x := fderiv ℝ f x, L_x := A_x ∘ ι_x, J*f(x) := coareaJacobian M f x = √det(L_x L_x*).

1. (Pointwise identity, every x ∈ ℝᴺ.) The adjoint of a composition is the reversed composition of adjoints, so L_x* = ι_x* ∘ A_x*. The adjoint of the inclusion ι_x is π_x: for t ∈ T_x and v ∈ ℝᴺ, ⟨ι_x t, v⟩ = ⟨t, π_x v⟩ because v − π_x v ⊥ T_x. Hence L_x L_x* = A_x ∘ ι_x ∘ π_x ∘ A_x* = A_x ∘ P_x ∘ A_x*, and J*f(x) = √det(A_x ∘ P_x ∘ A_x*) for every x.
2. (Continuity of the ingredients on M.) (a) f is C¹ on the open set U, so x ↦ A_x = Df(x) is continuous on U, hence on M ⊆ U. (b) B ↦ B* is a linear isometry (ℝᴺ →L ℝᵐ) → (ℝᵐ →L ℝᴺ), hence continuous; so x ↦ A_x* is continuous on M. (c) x ↦ P_x is continuous on M by hypothesis. (d) Composition of continuous linear maps is a bounded bilinear operation, hence jointly continuous; so x ↦ A_x ∘ P_x ∘ A_x* is continuous on M. (e) det : (ℝᵐ →L ℝᵐ) → ℝ is continuous (finite dimension) and √ : ℝ → ℝ is continuous.
3. By steps 1 and 2, J*f agrees on all of ℝᴺ with √ ∘ det ∘ (x ↦ A_x ∘ P_x ∘ A_x*), which is continuous on M. Hence J*f is continuous on M. This is the first conjunct.
4. (Relative closedness.) Fix y ∈ ℝᵐ and let S_y := M ∩ f⁻¹{y} ∩ {x : J*f(x) = 0}. f is continuous on U (C¹ implies continuous), hence on M. Claim: every x ∈ M ∩ closure(S_y) lies in S_y. Indeed choose x_j ∈ S_y with x_j → x (ℝᴺ is a metric space). All x_j and x lie in M, and f and J*f are continuous on M, so f(x) = lim f(x_j) = y and J*f(x) = lim J*f(x_j) = 0; thus x ∈ S_y.
5. Put F := closure(S_y), a closed subset of ℝᴺ. Then M ∩ F = S_y: "⊇" because S_y ⊆ M and S_y ⊆ closure(S_y); "⊆" by step 4. This is the second conjunct, for every y. ∎
(Equivalent route used in the checked Lean code: by the characterization of continuity on a subset, continuousOn_iff_isClosed, there are closed F₁, F₂ with J*f⁻¹{0} ∩ M = F₁ ∩ M and f⁻¹{y} ∩ M = F₂ ∩ M; then F := F₁ ∩ F₂ satisfies M ∩ f⁻¹{y} ∩ {J*f = 0} = M ∩ F by elementwise set algebra.)

Formalization reference (machine-checked by the decomposer with only `import GMT.Ch02.Submission`, inside `namespace GMT.Ch02` with the contract's opens; axioms propext, Classical.choice, Quot.sound only). Key library facts: ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL (U.subtypeL† = U.orthogonalProjectionOnto), Submodule.starProjection = subtypeL ∘L orthogonalProjectionOnto (definitional), ContDiffOn.continuousOn_fderiv_of_isOpen, ContinuousOn.clm_comp, ContinuousLinearMap.continuous_det, Real.continuous_sqrt, continuousOn_iff_isClosed.

```lean
theorem c1_sard_coarea_jacobian_continuousOn : ∀ (N m : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → ContinuousOn (tangentProjection M) M → ContinuousOn (coareaJacobian M f) M ∧ ∀ y : Rn m, ∃ F : Set (Rn N), IsClosed F ∧ M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0} = M ∩ F := by
  intro N m M U f hU hMU hf hP
  have key : ∀ x, coareaJacobian M f x = Real.sqrt (((fderiv ℝ f x) ∘L (tangentProjection M x ∘L ContinuousLinearMap.adjoint (fderiv ℝ f x))).det) := by
    intro x
    simp only [coareaJacobian]
    congr 2
    rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL]
    rfl
  have hJ : ContinuousOn (coareaJacobian M f) M := by
    have hD : ContinuousOn (fderiv ℝ f) M := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hMU
    have hDadj : ContinuousOn (fun x => ContinuousLinearMap.adjoint (fderiv ℝ f x)) M :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn N) (F := Rn m)).continuous.comp_continuousOn hD
    have hprod : ContinuousOn (fun x => (fderiv ℝ f x) ∘L (tangentProjection M x ∘L ContinuousLinearMap.adjoint (fderiv ℝ f x))) M :=
      hD.clm_comp (hP.clm_comp hDadj)
    have : ContinuousOn (fun x => Real.sqrt (((fderiv ℝ f x) ∘L (tangentProjection M x ∘L ContinuousLinearMap.adjoint (fderiv ℝ f x))).det)) M :=
      Real.continuous_sqrt.comp_continuousOn (ContinuousLinearMap.continuous_det.comp_continuousOn hprod)
    exact this.congr (fun x _ => key x)
  refine ⟨hJ, fun y => ?_⟩
  obtain ⟨F₁, hF₁, h₁⟩ := continuousOn_iff_isClosed.mp hJ {0} isClosed_singleton
  obtain ⟨F₂, hF₂, h₂⟩ := continuousOn_iff_isClosed.mp ((hf.continuousOn).mono hMU) {y} isClosed_singleton
  refine ⟨F₁ ∩ F₂, hF₁.inter hF₂, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxM, hxy⟩, hxZ⟩
    have h1 : x ∈ F₁ ∩ M := h₁ ▸ ⟨hxZ, hxM⟩
    have h2 : x ∈ F₂ ∩ M := h₂ ▸ ⟨hxy, hxM⟩
    exact ⟨hxM, h1.1, h2.1⟩
  · rintro ⟨hxM, hx1, hx2⟩
    have h1 : x ∈ coareaJacobian M f ⁻¹' {0} ∩ M := h₁.symm ▸ ⟨hx1, hxM⟩
    have h2 : x ∈ f ⁻¹' {y} ∩ M := h₂.symm ▸ ⟨hx2, hxM⟩
    exact ⟨⟨hxM, h2.1⟩, h1.1⟩
```

## Key steps

1. For every x, L_x L_x* = Df(x) ∘ P_x ∘ Df(x)* because the adjoint of the inclusion of T_xM is the orthogonal projection.
2. Df is continuous on U ⊇ M, P is continuous on M, and adjoint, composition, det and √ are continuous, so J*f is continuous on M.
3. By continuity of f and J*f on M, S_y = M ∩ f⁻¹{y} ∩ {J*f = 0} is relatively closed in M, so S_y = M ∩ closure(S_y) (equivalently M ∩ (F₁ ∩ F₂)).

## Reference use

### local-project

Queries:
- `rg -n "^def C1Sard|^def CoareaFormula|^def coareaJacobian|^def tangentSpace|^def tangentProjection" project/GMT/Ch02/Contract.lean`
- `rg -n "C1Sard|6.4" project/GMT/Ch02/README.md`
- `rg -n "theorem toOpenPartialHomeomorph|def toOpenPartialHomeomorph|theorem mem_toOpenPartialHomeomorph_source" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `rg -n "theorem OpenPartialHomeomorph.contDiffAt_symm" mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean; rg -n "theorem OpenPartialHomeomorph.hasFDerivAt_symm" mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `rg -n "protected theorem ContinuousLinearEquiv.isOpen" mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean; rg -n "protected def restrOpen|theorem coe_restrOpen" mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean`
- `rg -n "theorem _root_.Submodule.adjoint_subtypeL|theorem adjoint_comp|theorem _root_.ContinuousLinearMap.adjoint_toLinearMap" mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean; rg -n "^def starProjection|theorem orthogonalProjectionOnto_mem_subspace_eq_self" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "theorem ContinuousOn.clm_comp" mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean; rg -n "theorem ContDiffOn.continuousOn_fderiv_of_isOpen" mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean; rg -n "theorem continuousOn_iff_isClosed|theorem ContinuousOn.isOpen_inter_preimage" mathlib/Mathlib/Topology/ContinuousOn.lean`
- `rg -n "theorem lintegral_eq_zero_iff'|theorem lintegral_indicator_one" mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean`
- `rg -n "theorem finrank_range_add_finrank_ker|theorem injective_iff_surjective_of_finrank_eq_finrank" mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean; rg -n "lemma ball_prod_same" mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean; rg -n "theorem fderiv_comp " mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean; rg -n "theorem finrank_euclideanSpace_fin" mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n "def implicitToOpenPartialHomeomorph|def implicitFunction|theorem map_implicitFunction_eq" mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `rg -il "sard" mathlib/Mathlib; rg -n "Submission\." project --glob '*.lean'; rg -il "sard|regular value|implicit" lake-packages-25730c7c/simongmt/Poincare/SimonGMT/`
- `full reads of simongmt Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldTopology,SubmanifoldCalculus,CoareaLinearAlgebra,CoareaProjection}.lean; git rev-parse HEAD of the simongmt and mathlib package checkouts`
- `python3 -I gen_checks.py / gen_solutions.py (replay verifier gmt-compare.py contract_scope + child_modules for the six lean_statements); lean NodeChallenge/NodeSolution modules against scratch oleans of GMT.Ch02.Submission`
- `lean Assembly.lean, GCheck.lean, Combined.lean with #print axioms (six child proofs + parent assembly, uncle types as stand-ins)`
- `read dag.json lean_name list for collisions with the six proposed names`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-sard-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/c1sard-decomp-Z3BOJI/Combined.lean`

Frozen contract: Contract.lean:349-374 fixes CoareaFormula and C1Sard. Conjunct (2) uses μHE[k] and volume on Rn m, and conjunct (3b) uses IsSimonSubmanifold (E := Rn k) 1. coareaJacobian (line 123) is defined with ContinuousLinearMap.adjoint and the det of L ∘L L†. README row 16 and line 103 confirm the relatively-closed reading and the rank conjunct.

Snapshot Mathlib supplies everything the six children use:
- the C¹ inverse function theorem, ContDiffAt.toOpenPartialHomeomorph (InverseFunctionTheorem/ContDiff.lean:31);
- OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881) and OpenPartialHomeomorph.hasFDerivAt_symm (FDeriv/OfCompLeft.lean:214);
- ContinuousLinearEquiv.isOpen (BoundedLinearMaps.lean:543) and restrOpen (OpenPartialHomeomorph/IsImage.lean:216; its coercions are rfl);
- Submodule.adjoint_subtypeL (Adjoint.lean:177), adjoint_comp (Adjoint.lean:136) and starProjection (Projection/Basic.lean:131);
- ContinuousOn.clm_comp (BoundedLinearMaps.lean:453), ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916) and continuousOn_iff_isClosed (Topology/ContinuousOn.lean:149);
- lintegral_eq_zero_iff' and lintegral_indicator_one (Lebesgue/Basic.lean:322, 572);
- rank-nullity (FiniteDimensional/Lemmas.lean:173, 204), ball_prod_same, fderiv_comp and finrank_euclideanSpace_fin.

No existing result proves C1Sard or any child. Implicit.lean offers an alternative implicit-function route. The 'Sard' matches (MeasureTheory/Function/Jacobian.lean) are the equal-dimension critical-value lemma, not the coarea-based C¹ Sard theorem. The SimonGMT 'implicit' matches are unrelated comments.

Pinned SimonGMT is at rev 2b3663083f3f, which matches the lakefile, and its oleans are built. It provides:
- coareaLinearJacobian_eq_sqrt_det and coareaLinearJacobian_eq_zero_iff (CoareaLinearAlgebra.lean:35-48);
- IsSimonLocalRepresentation.exists_open_image_eq_inter (SubmanifoldTopology.lean:100, Simon 4.2).
All of these depend only on propext, Classical.choice and Quot.sound.

The project snapshot has no Submission.* declarations, and dag.json has no c1_sard_* children, so the six names are free.

Verifier replay results:
- all six statements elaborate after import GMT.Ch02.Submission in the contract scope;
- the assembly proves C1Sard from the children and the two uncle types;
- complete Lean proofs of all six children compile, and the verifier-generated NodeSolution modules check against them using standard axioms only.
