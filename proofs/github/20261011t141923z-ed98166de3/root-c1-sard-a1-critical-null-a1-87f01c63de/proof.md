# Parent-supplied natural-language proof

- Parent DAG node: `root.c1_sard-a1`
- Child DAG node: `root.c1_sard-a1.critical_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof of root.c1_sard-a1, PART II steps 3-4 (Simon, Ch. 2 §6, p. 66: "An important consequence of 6.3 is that if C = {x ∈ M : J*f(x) = 0}, then (by using 6.3 with A = C) Hᵏ(C ∩ f⁻¹(y)) = 0 for Lᵐ-a.e. y ∈ ℝᵐ"). The co-area formula enters only through the hypothesis CoareaFormula (frozen contract definition; in the parent it is supplied by the sibling node coarea_formula), and the measurability of M and continuity of J*f on M are hypotheses (supplied in the parent by submanifold_tangent and jacobian_continuity).

Notation. J*f(x) := coareaJacobian M f x, Z := {x : J*f(x) = 0}, C := M ∩ Z, Hᵏ := μHE[k], Lᵐ := volume on ℝᵐ.

1. (C is measurable.) J*f is continuous on M and {0} ⊆ ℝ is closed, so the relative preimage is relatively closed: there is a closed F₀ ⊆ ℝᴺ with J*f⁻¹{0} ∩ M = F₀ ∩ M (continuousOn_iff_isClosed). Hence C = M ∩ F₀, which is measurable as the intersection of the measurable set M (hypothesis) with the closed, hence Borel, set F₀.
2. (The weight.) Let g := 1_C : ℝᴺ → [0, ∞], the indicator function of C. g is measurable (indicator of a measurable set), hence AEMeasurable for μHE[m+k] restricted to M.
3. (Co-area formula.) CoareaFormula applied to N, m, k, M, U, f, g (its hypotheses 0 < k, IsSimonSubmanifold (E := ℝ^{m+k}) 1 M, IsOpen U, M ⊆ U, ContDiffOn ℝ 1 f U and AEMeasurable g hold) gives: (i) I(y) := ∫_{M ∩ f⁻¹{y}} g dHᵏ defines an AEMeasurable function of y for Lᵐ; (ii) ∫_M g(x)·ofReal(J*f(x)) dH^{m+k}(x) = ∫ I(y) dLᵐ(y).
4. (Left side is 0.) The integrand x ↦ g(x)·ofReal(J*f(x)) vanishes at every x ∈ ℝᴺ: if x ∈ C then J*f(x) = 0 and ofReal 0 = 0; if x ∉ C then g(x) = 0. Hence the left side of (ii) is the integral of 0, so ∫ I dLᵐ = 0.
5. (A.e. vanishing.) I is AEMeasurable and has zero lintegral, so I(y) = 0 for Lᵐ-a.e. y (lintegral_eq_zero_iff').
6. (Identify I.) For every y, since C is measurable, I(y) = ∫ 1_C d(Hᵏ restricted to M ∩ f⁻¹{y}) = Hᵏ(C ∩ (M ∩ f⁻¹{y})) (lintegral_indicator_one, Measure.restrict_apply). Moreover C ∩ (M ∩ f⁻¹{y}) = M ∩ f⁻¹{y} ∩ Z, both being {x ∈ M : f(x) = y, J*f(x) = 0}.
7. By steps 5 and 6, for Lᵐ-a.e. y ∈ ℝᵐ, μHE[k](M ∩ f⁻¹{y} ∩ {x | coareaJacobian M f x = 0}) = 0. ∎

Formalization reference (machine-checked by the decomposer with only `import GMT.Ch02.Submission`, inside `namespace GMT.Ch02` with the contract's opens; axioms propext, Classical.choice, Quot.sound only). Note: CoareaFormula is a Prop-valued def, so the hypothesis `hco : CoareaFormula` is applied directly as `hco N m k M U f g hk hM hU hMU hf hgm`.

```lean
theorem c1_sard_critical_fibers_null : CoareaFormula → ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), 0 < k → Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → MeasurableSet M → ContinuousOn (coareaJacobian M f) M → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}) = 0 := by
  intro hco N m k M U f hk hM hU hMU hf hMmeas hJ
  obtain ⟨F₀, hF₀, h₀⟩ := continuousOn_iff_isClosed.mp hJ {0} isClosed_singleton
  set C : Set (Rn N) := M ∩ {x | coareaJacobian M f x = 0} with hCdef
  have hC : C = M ∩ F₀ := by
    ext x; constructor
    · rintro ⟨hxM, hx⟩
      have : x ∈ F₀ ∩ M := h₀ ▸ ⟨hx, hxM⟩
      exact ⟨hxM, this.1⟩
    · rintro ⟨hxM, hx⟩
      have : x ∈ coareaJacobian M f ⁻¹' {0} ∩ M := h₀.symm ▸ ⟨hx, hxM⟩
      exact ⟨hxM, this.1⟩
  have hCmeas : MeasurableSet C := hC ▸ hMmeas.inter hF₀.measurableSet
  set g : Rn N → ℝ≥0∞ := C.indicator 1 with hg
  have hgm : AEMeasurable g (μHE[m + k].restrict M) := (measurable_one.indicator hCmeas).aemeasurable
  obtain ⟨hAEM, hEq⟩ := hco N m k M U f g hk hM hU hMU hf hgm
  have hLHS : (fun x => g x * ENNReal.ofReal (coareaJacobian M f x)) = 0 := by
    funext x
    by_cases hx : x ∈ C
    · have hx2 : coareaJacobian M f x = 0 := hx.2
      simp [hx2]
    · simp [g, hx]
  rw [hLHS] at hEq
  have hEq0 : ∫⁻ y, ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂(volume : Measure (Rn m)) = 0 := by
    rw [← hEq]; exact lintegral_zero
  have hae := (lintegral_eq_zero_iff' hAEM).mp hEq0
  filter_upwards [hae] with y hy
  have hinner : ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] = μHE[k] (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}) := by
    rw [lintegral_indicator_one hCmeas, Measure.restrict_apply hCmeas]
    congr 1
    ext x; constructor
    · rintro ⟨⟨hxM, hxZ⟩, hxM', hxy⟩; exact ⟨⟨hxM, hxy⟩, hxZ⟩
    · rintro ⟨⟨hxM, hxy⟩, hxZ⟩; exact ⟨⟨hxM, hxZ⟩, hxM, hxy⟩
  rw [← hinner]; exact hy
```

## Key steps

1. C := M ∩ {J*f = 0} = M ∩ F₀ with F₀ closed (continuity of J*f on M), so C is measurable.
2. Apply CoareaFormula with g = 1_C; the left integrand 1_C · ofReal(J*f) vanishes identically, so ∫ I(y) dy = 0.
3. I is AEMeasurable with zero integral, so I(y) = 0 for a.e. y (lintegral_eq_zero_iff').
4. I(y) = μHE[k](C ∩ (M ∩ f⁻¹{y})) = μHE[k](M ∩ f⁻¹{y} ∩ {J*f = 0}).

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
