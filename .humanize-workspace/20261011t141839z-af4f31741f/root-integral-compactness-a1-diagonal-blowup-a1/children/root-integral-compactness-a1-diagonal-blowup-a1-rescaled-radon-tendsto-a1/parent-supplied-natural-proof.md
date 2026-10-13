# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.diagonal_blowup-a1`
- Child DAG node: `root.integral_compactness-a1.diagonal_blowup-a1.rescaled_radon_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0(a)–0(b) of the parent proof; this is the parenthetical remark in the printed proof of Simon 8.5.9 "because V_i → V, and hence η_{ξ,λ#}V_i → η_{ξ,λ#}V for each fixed λ > 0". Notation: G := Grassmannian N n, Z := ℝ^N × G; for a varifold V' on U, V'_{ξ,t} := rescaledMeasure V' ξ t = ofReal(t⁻¹^n) • (V'.measure).map Φ, where Φ(z) := (t⁻¹ • (z.1 − ξ), z.2).

1. (Φ is a homeomorphism.) Put Ψ(z) := (ξ + t • z.1, z.2). Φ and Ψ are continuous, and Ψ ∘ Φ = id, Φ ∘ Ψ = id because t ≠ 0 (t⁻¹ • t = 1). Hence Φ is a homeomorphism of Z; in particular Φ is Borel measurable and is a cocompact map (Homeomorph.toCocompactMap).

2. (Pulled-back test function.) Let H := F ∘ Φ. Composition of a compactly supported continuous function with a cocompact map is compactly supported (CompactlySupportedContinuousMap.comp F Φ.toCocompactMap), so H ∈ C_c(Z, ℝ). Since Φ is continuous, tsupport H ⊆ Φ⁻¹(tsupport F) (tsupport_comp_subset_preimage). If z ∈ tsupport H then Φ z ∈ tsupport F, and the hypothesis applied to Φ z gives ξ + t • (t⁻¹ • (z.1 − ξ)) = z.1 ∈ U. Hence tsupport H ⊆ U ×ˢ univ, and tsupport H is compact.

3. (Rescaling formula.) For every varifold V' on U: ∫ F dV'_{ξ,t} = t⁻¹^n · ∫ H dV'.measure. Indeed ∫ F d(c • μ) = c.toReal · ∫ F dμ for every c ∈ [0,∞] (integral_smul_measure), (ofReal(t⁻¹^n)).toReal = t⁻¹^n because t⁻¹^n ≥ 0 (ENNReal.toReal_ofReal), and ∫ F d(μ.map Φ) = ∫ F(Φ z) dμ(z) (integral_map; Φ is measurable and F is continuous, hence a.e. strongly measurable). No integrability is needed for these identities.

4. (Restriction to Simon's open product.) Let Ω := U ×ˢ (univ : Set G). U is open (V.isOpen_domain), so Ω is open and measurable; let ι : Ω → Z be the inclusion and h := H ∘ ι : Ω → ℝ. h is continuous. Its support is contained in ι⁻¹(tsupport H), which is closed in Ω, so tsupport h ⊆ ι⁻¹(tsupport H) (tsupport_comp_subset_preimage); and ι⁻¹(tsupport H) is compact, because tsupport H is compact and contained in range ι = Ω (step 2) and ι is an embedding (Topology.IsInducing.subtypeVal.isCompact_preimage'). Hence h has compact support, i.e. h ∈ C_c(Ω, ℝ). (This is the construction of SimonGMT Varifold.divergenceDomainTest.)

5. (Domain integrals.) For every varifold V' on U: ∫ h d(V'.domainMeasure) = ∫ H dV'.measure. Indeed V'.measure = (V'.domainMeasure).map ι (Varifold.map_domainMeasure), and ι is a measurable embedding (MeasurableEmbedding.subtype_coe for the measurable set Ω), so ∫ H d((V'.domainMeasure).map ι) = ∫ H(ι w) d(V'.domainMeasure)(w) (MeasurableEmbedding.integral_map). (Compare Varifold.integral_divergenceDomainTest.)

6. (Conclusion.) By the definition of Varifold.RadonConverges applied to h ∈ C_c(Ω, ℝ), ∫ h d((Vi i).domainMeasure) → ∫ h d(V.domainMeasure) as i → ∞. Multiplying by the constant t⁻¹^n (Tendsto.const_mul) and rewriting both sides with step 5 and then step 3 (for V' = Vi i and for V' = V) gives ∫ F d(Vi i)_{ξ,t} → ∫ F dV_{ξ,t}. ∎

Lean realization (informative; compiled during decomposition, complete, depending only on the axioms propext, Classical.choice, Quot.sound, against the pinned toolchain, placed in GMT/Ch08/Submission.lean inside `namespace GMT.Ch08` after `end Definitions`, i.e. in the frozen contract scope `open Set Filter MeasureTheory Metric`, `open scoped Topology ENNReal CompactlySupported Pointwise`, `open Poincare.SimonGMT`, `open Poincare.SimonGMT.Chapter08`; scratch copy /tmp/diagdecomp/FullCheck.lean):

theorem Submission.intcpt_diag_rescaled_radon_tendsto : ∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U) (ξ : Euclidean N) (t : ℝ) (F : C_c(Euclidean N × Grassmannian N n, ℝ)), Varifold.RadonConverges Vi V → 0 < t → (∀ z ∈ tsupport F, ξ + t • z.1 ∈ U) → Tendsto (fun i ↦ ∫ z, F z ∂(rescaledMeasure (Vi i) ξ t)) atTop (𝓝 (∫ z, F z ∂(rescaledMeasure V ξ t))) := by
  intro N n U Vi V ξ t F hconv ht hF
  let Φ : Euclidean N × Grassmannian N n ≃ₜ Euclidean N × Grassmannian N n :=
    { toFun := fun z ↦ (t⁻¹ • (z.1 - ξ), z.2)
      invFun := fun z ↦ (ξ + t • z.1, z.2)
      left_inv := by
        intro z
        ext1
        · simp [smul_smul, ht.ne']
        · rfl
      right_inv := by
        intro z
        ext1
        · simp [smul_smul, ht.ne']
        · rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let H : C_c(Euclidean N × Grassmannian N n, ℝ) := F.comp Φ.toCocompactMap
  have hH : ∀ z, H z = F (Φ z) := fun z ↦ rfl
  have hHsupp : tsupport H ⊆ U ×ˢ (univ : Set (Grassmannian N n)) := by
    intro z hz
    have hz' : Φ z ∈ tsupport F := tsupport_comp_subset_preimage F Φ.continuous hz
    refine ⟨?_, trivial⟩
    have := hF _ hz'
    simpa [Φ, smul_smul, ht.ne'] using this
  have hresc : ∀ V' : Varifold N n U,
      ∫ z, F z ∂(rescaledMeasure V' ξ t) = t⁻¹ ^ n * ∫ z, H z ∂V'.measure := by
    intro V'
    have hm : Continuous (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - ξ), z.2)) := by
      fun_prop
    rw [rescaledMeasure, integral_smul_measure,
      integral_map hm.measurable.aemeasurable (map_continuous F).aestronglyMeasurable,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    rfl
  let Ω := U ×ˢ (univ : Set (Grassmannian N n))
  let h : C_c(Ω, ℝ) :=
    { toFun := fun w ↦ H w.1
      continuous_toFun := H.continuous.comp continuous_subtype_val
      hasCompactSupport' := by
        have hK : IsCompact ((Subtype.val : Ω → Euclidean N × Grassmannian N n) ⁻¹' tsupport H) :=
          Topology.IsInducing.subtypeVal.isCompact_preimage' H.hasCompactSupport.isCompact (by
            intro z hz
            exact ⟨⟨z, hHsupp hz⟩, rfl⟩)
        exact hK.of_isClosed_subset (isClosed_tsupport _)
          (tsupport_comp_subset_preimage H continuous_subtype_val) }
  have hdom : ∀ V' : Varifold N n U, ∫ w, h w ∂V'.domainMeasure = ∫ z, H z ∂V'.measure := by
    intro V'
    rw [← V'.map_domainMeasure, (MeasurableEmbedding.subtype_coe
      (V'.isOpen_domain.measurableSet.prod MeasurableSet.univ)).integral_map]
    rfl
  have := (hconv h).const_mul (t⁻¹ ^ n)
  simp only [hdom] at this
  simpa only [hresc] using this

## Key steps

1. Φ(z,S) = (t⁻¹(z−ξ), S) is a homeomorphism of ℝ^N × G with inverse (y,S) ↦ (ξ+ty, S).
2. H := F ∘ Φ ∈ C_c(ℝ^N × G) and tsupport H ⊆ U × G by the support hypothesis.
3. Rescaling formula: ∫ F dV'_{ξ,t} = t^{-n} ∫ H dV'.measure for every varifold V' on U (integral_smul_measure, integral_map).
4. The restriction h := H|_{U×G} is in C_c(U × G) (subtype embedding, compact preimage).
5. ∫ h d(V'.domainMeasure) = ∫ H dV'.measure (map_domainMeasure, MeasurableEmbedding.integral_map).
6. Apply RadonConverges to h and multiply by t^{-n}.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean (2e5cd5b3…, identical to workspace GMT/Ch08/Contract.lean and Submission.lean)`
- `rg -n 'theorem integral_smul_measure|theorem integral_map |theorem _root_.MeasurableEmbedding.integral_map|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem ofReal_integral_eq_lintegral_ofReal|theorem norm_setIntegral_le_of_norm_le_const|lemma Measure.integrableOn_of_bounded|theorem integrableOn_iff_integrable_of_support_subset|theorem Integrable.smul_measure|theorem integrable_map_measure|theorem eventually_all_finset|theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem tendsto_measure_iUnion_atTop|theorem _root_.Monotone.measure_iUnion|lemma Topology.IsInducing.isCompact_preimage|theorem Countable.exists_eq_range|theorem dist_apply_le_dist|theorem hasBasis_compactConvergenceUniformity|def toCocompactMap|theorem restrict_apply_self|theorem lintegral_indicator_one' mathlib/Mathlib`
- `grep -rn 'theorem exists_continuous_one_zero_of_isCompact|theorem Frequently.and_eventually|frequently_lt_of_liminf_lt|Filter.Tendsto.eventually_const_lt (to_dual eventually_lt_const)|theorem exists_countable_dense_subset|IsSeparable.exists_countable_dense_subset' mathlib/Mathlib`
- `grep -rn 'SeparableSpace C(|SecondCountableTopology C(' mathlib/Mathlib/Topology mathlib/Mathlib/Analysis (only ContinuousMap/SecondCountableSpace.lean)`
- `sed CompactlySupported.lean (CompactlySupportedContinuousMap.comp with →co, Mul/smul instances) and CocompactMap.lean (Homeomorph.toCocompactMap)`
- `grep -n in simongmt Chapter08/{Varifold,VarifoldConvergence,FirstVariationRiesz,FirstVariationBounds,TangentRescaling}.lean, Chapter04/WeightedBlowUp.lean, Chapter03/Rectifiable.lean: structure Varifold, domainMeasure, map_domainMeasure, RadonConverges, divergenceDomainTest, integral_divergenceDomainTest, TestVectorField, firstVariationNormOn, le_firstVariationNormOn, firstVariationNormOn_le_of_polarRepresentation, isFirstVariationPolarRepresentation_riesz, firstVariationRieszMeasure_eq_norm, tangentialDivergence, jacobian, clmToMatrix, support_tangentialDivergence_subset, continuous_tangentialDivergence, blowUpMeasure, blowUp, blowUpHomeomorph, blowUpMap, Grassmannian.instCompactSpace/instSecondCountableTopology`
- `lake env lean /tmp/diagdecomp/{Inst,Avail,Avail2}.lean (#check under import GMT.Ch08.Submission: SecondCountableTopology C(L,ℝ) and SeparableSpace C(L,ℝ) fail; Chapter04.blowUpHomeomorph and Varifold.blowUpMeasure unknown; Stone–Weierstrass, Urysohn, denseSeq, compact-convergence uniformity available)`
- `git show 2721e20337252ca8e1f6204843570bd04ba673c8:GMT/Ch08/Submission.lean (accepted Submission.radon_compactlySupported_countable_approx: inlined second countability of C(X,ℝ))`
- `python3 verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch08.main_theorem); verifier/lean_contract.py validate_lean_statement on the 5 lean_statements`
- `lake env lean /tmp/diagdecomp/Chal_*.lean (comparator form) and /tmp/diagdecomp/FullCheck.lean (#print axioms)`
- `grep 'intcpt_diag_' in dag.json and nodes/*; git grep over all 107 local branches and remotes (no matches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/CocompactMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UniformSpace/CompactConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/Filter/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRescaling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-diagonal-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1/decomposition-v1.json`
- `/tmp/diagdecomp/FullCheck.lean`
- `/tmp/diagdecomp/AssemblyFinal.lean`

Snapshot = project 63436ae6 + Mathlib 25730c7c; its Contract is byte-identical to the workspace Contract and Submission (sha256 2e5cd5b3…). Mathlib has no varifold theory, so the Ch. 8 objects come from the pinned SimonGMT package. SimonGMT already supplies the facts the children need: domainMeasure/map_domainMeasure and divergenceDomainTest, used for the transfer in child (1); RadonConverges; TestVectorField and firstVariationNormOn with le_firstVariationNormOn; the Riesz identities firstVariationRieszMeasure_eq_norm and isFirstVariationPolarRepresentation_riesz with firstVariationNormOn_le_of_polarRepresentation, used in child (4); and the Grassmannian compactness and second-countability instances. These are standard-axiom declarations reachable from `import GMT.Ch08.Submission`. TangentRescaling (blowUpMeasure, definitionally the contract's rescaledMeasure) and Chapter04.blowUpHomeomorph are NOT imported, so the children build the dilation homeomorphism directly. Every Mathlib lemma cited in the child proofs exists in the snapshot with matching hypotheses. The exception is second countability of C(X,ℝ), which sits in a non-imported file and is therefore inlined in child (3), as in the accepted radon_compactlySupported_countable_approx (commit 2721e203). The 5 child statements elaborate in comparator form, and the 5 children were proved completely in Lean with only propext, Classical.choice and Quot.sound. The parent assembly compiles from them plus the sibling rescaled_integral stub, with sorryAx only through that stub. No intcpt_diag_* name is reserved anywhere.
