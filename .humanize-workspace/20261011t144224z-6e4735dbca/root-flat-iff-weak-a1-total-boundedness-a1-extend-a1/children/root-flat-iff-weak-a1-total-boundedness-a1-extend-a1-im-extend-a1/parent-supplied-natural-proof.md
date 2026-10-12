# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.im_extend-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9 (Lemma B, (B1)–(B5)) of the parent proof.
- In (B2), the support-null fact H^q(M ∖ spt(Z|_U)) = 0 comes from the reused sibling rect_support_null (Submission.lpf_rectifiable_support_null). It has the same conclusion as the parent's sibling support_null, but no MF hypothesis.
- In (B3)–(B4), the blow-up/tangent congruence is the reused sibling tangent_congr (Submission.br_weightedTangent_congr). As the parent's Remark indicates, the special case used is V := ℝ^P, M' := M ∩ K, θ' := θ.

Notation.
- H := H^q = μHE[q], and H⌞A := H.restrict A.
- τ(M, θ, ξ)(φ) := tauAction q M θ ξ φ = ∫_M θ(x)·ξ(x)(φ(x)) dH(x).
- ι := testFormOnInclusion (subset_univ U) q; it does not change the underlying form.

1. (Data.) By hypothesis there are M, θ, ξ with:
   - IsRectifiableTriple U q M θ ξ;
   - θ(x) ∈ ℕ for every x ∈ M;
   - Z|_U(ω) = τ(M, θ, ξ)(ω) for every ω ∈ D^q(U).
2. ((B1): spt(Z|_U) ⊆ K.) Let ω ∈ D^q(U) with tsupport ω disjoint from K. Then Z|_U(ω) = Z(ιω) = 0 by the hypothesis on Z, since ιω has the same underlying form and hence the same tsupport. U is open, and K is closed (compact in the Hausdorff space ℝ^P). So the sibling support_subset with V := U gives spt(Z|_U) ⊆ K.
3. ((B2): H(M ∖ K) = 0.) The reused sibling rect_support_null, applied to T := Z|_U and the triple of step 1, gives H(M ∖ spt(Z|_U)) = 0. By step 2, M ∖ K ⊆ M ∖ spt(Z|_U), so H(M ∖ K) = 0 (measure_mono_null).
4. Put M' := M ∩ K.
   - M' ∖ M = ∅, and M ∖ M' = M ∖ K is H-null. So M' and M are H-a.e. equal (ae_eq_set), and H⌞M' = H⌞M (Measure.restrict_congr_set).
   - symmDiff M M' = (M ∖ M') ∪ (M' ∖ M) ⊆ M ∖ K, hence H(symmDiff M M' ∩ ℝ^P) = 0.
5. ((B3)–(B4): (M', θ, ξ) is a rectifiable triple in ℝ^P.) We verify the seven fields of IsRectifiableTriple univ q M' θ ξ.
   (a) subset: M' ⊆ ℝ^P = univ.
   (b) nullMeasurableSet: M is H-null-measurable and K is closed, hence measurable. So M' = M ∩ K is H-null-measurable (NullMeasurableSet.inter).
   (c) countablyRectifiable: M' ⊆ M, and M is countably q-rectifiable (CountablyRectifiable.mono).
   (d) pos: θ > 0 on M ⊇ M'.
   (e) integrableOn: let K'' ⊆ ℝ^P be compact. θ is H-integrable on M ∩ K, because K is a compact subset of U (field integrableOn of the U-triple). Since M' ∩ K'' ⊆ M ∩ K, θ is H-integrable on M' ∩ K'' (IntegrableOn.mono_set).
   (f) aestronglyMeasurable: ξ is a.e. strongly measurable for H⌞M = H⌞M' (step 4).
   (g) orients: since H⌞M' = H⌞M, it suffices to show the following for H⌞M-a.e. x: there is an orthonormal τ : Fin q → ℝ^P with HasWeightedApproximateTangentSpaceAt q M' θ x (span(range τ)) and ξ(x) = ±simpleNVector τ.
       - The U-triple gives, for H⌞M-a.e. x, an orthonormal τ with HasWeightedApproximateTangentSpaceAt q M θ x (span(range τ)) and ξ(x) = ±simpleNVector τ.
       - For such x, apply the reused sibling tangent_congr with (M, M', θ, θ', x, V) := (M, M', θ, θ, x, ℝ^P). Its hypotheses hold: ℝ^P is open and contains x; H(symmDiff M M' ∩ ℝ^P) = 0 by step 4; θ = θ everywhere; θ(x) = θ(x).
       - It gives HasWeightedApproximateTangentSpaceAt q M' θ x (span(range τ)), so the same τ works (filter_upwards).
6. (Integrality.) For x ∈ M' ⊆ M, θ(x) ∈ ℕ by step 1.
7. ((B5): representation.)
   - The sibling cutoff gives a C^∞ χ with tsupport χ ⊆ U and an open N ⊇ K with χ = 1 on N.
   - The sibling smul_testform (V := ℝ^P, W := U) gives a linear L : D^q(ℝ^P) → D^q(U) with (Lω)(x) = χ(x)·ω(x).
   Let ω ∈ D^q(ℝ^P).
   (a) ι(Lω) and ω agree on N, because χ = 1 there. So the sibling eq_near (V := ℝ^P, with the vanishing hypothesis on Z) gives Z(ω) = Z(ι(Lω)) = Z|_U(Lω).
   (b) By step 1 and H⌞M = H⌞M' (step 4): Z|_U(Lω) = ∫_M θ(x)·ξ(x)(χ(x)ω(x)) dH(x) = ∫_{M'} θ(x)·ξ(x)(χ(x)ω(x)) dH(x).
   (c) For x ∈ M' we have x ∈ K ⊆ N, so χ(x) = 1 and θ(x)·ξ(x)(χ(x)ω(x)) = θ(x)·ξ(x)(ω(x)). M' is H-null-measurable (5(b)), so setIntegral_congr_fun₀ gives ∫_{M'} θ·ξ(χω) dH = ∫_{M'} θ·ξ(ω) dH = τ(M', θ, ξ)(ω).
   Hence Z(ω) = τ(M', θ, ξ)(ω) for every ω ∈ D^q(ℝ^P).
8. By steps 5, 6 and 7, (M', θ, ξ) witnesses IsIntegerMultiplicity Z. ∎

Reference Lean proof (kernel-checked in a scratch build importing GMT.Ch06.Submission, in the comparator's contract scope; sibling dependencies are referenced as Submission.X):
theorem Submission.fiw_tb_ext_isIntegerMultiplicity : ∀ (P q : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ Z : GeometricCurrentOn (univ : Set (Eucl P)) q, (∀ ω : TestFormOn (univ : Set (Eucl P)) q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → IsIntegerMultiplicity (Z.restrictDomain (subset_univ U)) → IsIntegerMultiplicity Z := by
  intro P q U K hU hK hKU Z hZ hIM
  obtain ⟨M, θ, ξ, htri, hθN, hrep⟩ := hIM
  have hZUv : ∀ ω : TestFormOn U q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K →
      (Z.restrictDomain (subset_univ U)) ω = 0 := fun ω hω => hZ _ hω
  have hsptU : (Z.restrictDomain (subset_univ U)).support ⊆ K :=
    Submission.fiw_tb_ext_support_subset P q U K _ hU hK.isClosed hZUv
  have hnull : (μHE[q] : Measure (Eucl P)) (M \ K) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right hsptU)
      (Submission.lpf_rectifiable_support_null P q U _ M θ ξ htri hrep)
  have hae : (M ∩ K : Set (Eucl P)) =ᵐ[(μHE[q] : Measure (Eucl P))] M := by
    rw [ae_eq_set]
    constructor
    · exact measure_mono_null (fun x hx => (hx.2 hx.1.1).elim) measure_empty
    · simpa [sdiff_inter_self_eq_sdiff] using hnull
  have hrestr : (μHE[q] : Measure (Eucl P)).restrict (M ∩ K) =
      (μHE[q] : Measure (Eucl P)).restrict M := Measure.restrict_congr_set hae
  have hsymm : (μHE[q] : Measure (Eucl P)) (symmDiff M (M ∩ K) ∩ univ) = 0 := by
    refine measure_mono_null (fun x hx => ?_) hnull
    rcases hx.1 with ⟨hxM, hxMK⟩ | ⟨hxMK, hxM⟩
    · exact ⟨hxM, fun hxK => hxMK ⟨hxM, hxK⟩⟩
    · exact absurd hxMK.1 hxM
  have htri' : IsRectifiableTriple (univ : Set (Eucl P)) q (M ∩ K) θ ξ :=
    { subset := subset_univ _
      nullMeasurableSet := htri.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
      countablyRectifiable := htri.countablyRectifiable.mono inter_subset_left
      pos := fun x hx => htri.pos x hx.1
      integrableOn := fun K'' _ _ =>
        (htri.integrableOn K hK hKU).mono_set inter_subset_left
      aestronglyMeasurable := by rw [hrestr]; exact htri.aestronglyMeasurable
      orients := by
        rw [hrestr]
        filter_upwards [htri.orients] with x hx
        obtain ⟨τ, hτ, htan, hξ⟩ := hx
        exact ⟨τ, hτ, Submission.br_weightedTangent_congr P q M (M ∩ K) θ θ x univ isOpen_univ
          (mem_univ x) hsymm (ae_of_all _ fun _ => rfl) rfl _ htan, hξ⟩ }
  refine ⟨M ∩ K, θ, ξ, htri', fun x hx => hθN x hx.1, fun ω => ?_⟩
  obtain ⟨χ, N, hχs, -, -, hχU, hN, hKN, hχN⟩ := Submission.fiw_tb_ext_cutoff P U K hU hK hKU
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P q (univ : Set (Eucl P)) U χ hχs hχU
  have h1 : Z ω = Z (testFormOnInclusion (subset_univ U) q (L ω)) :=
    (Submission.fiw_tb_ext_apply_eq_of_eqOn P q univ K N Z hN hKN hZ ω _ (fun x hx => by
      change (L ω : DifferentialForm (Eucl P) q) x = _
      rw [hL, hχN x hx, one_smul])).symm
  rw [h1, ← GeometricCurrentOn.restrictDomain_apply, hrep]
  unfold tauAction
  rw [← hrestr]
  apply setIntegral_congr_fun₀ htri'.nullMeasurableSet
  intro x hx
  change θ x * ξ x ((L ω : DifferentialForm (Eucl P) q) x) = _
  rw [hL, hχN x (hKN hx.2), one_smul]

## Key steps

1. (B1): Z|_U vanishes off K, so spt(Z|_U) ⊆ K by support_subset (U open).
2. (B2): rect_support_null gives H^q(M ∖ spt(Z|_U)) = 0. Hence H^q(M ∖ K) = 0 and H^q⌞(M ∩ K) = H^q⌞M.
3. (B3)–(B4): (M ∩ K, θ, ξ) is a rectifiable triple in ℝ^P; the orientation transfers by tangent_congr with V = ℝ^P.
4. (B5): Z(ω) = Z|_U(χω) (eq_near) = ∫_M θξ(χω) = ∫_{M∩K} θξ(ω), since χ = 1 on K.
5. Hence Z = τ(M ∩ K, θ, ξ) with integer θ, so IsIntegerMultiplicity Z.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c95, Mathlib 25730c7c); diff -q snapshot project/GMT/Ch06/{Contract,Submission}.lean against the workspace (identical; HEAD d8d46c95, clean)`
- `grep -n '^open|^namespace|^end|^noncomputable|^def|^structure|^abbrev|^theorem' GMT/Ch06/Contract.lean (comparator scope; IsRectifiableTriple, tauAction, IsIntegerMultiplicity)`
- `grep -n '^structure|^def|^abbrev|^theorem|^@[simp] theorem' in SimonGMT Chapter06 Currents.lean, Mass.lean, CurrentLocalEquality.lean, Forms.lean (TestFormOn, TestFormOnConverges, GeometricCurrentOn, boundary_apply, tsupport_exteriorDerivative_subset, GeometricCurrentOn.ext, massAdmissibleOn, massOn, mass, le_massOn, covectorEuclideanNorm, testFormOnInclusion, restrictDomain_apply, VanishesOn, zeroRegion, support, IsSmoothForm, IsTestForm)`
- `grep -rn 'covectorEuclideanNorm_smul' SimonGMT (no match; only covectorEuclideanNorm_zero/_nonneg/_neg); grep CountablyRectifiable.mono in Chapter03/Rectifiable.lean`
- `grep -rn 'theorem exists_contDiff\w*|theorem exists_smooth\w*|theorem exists_contMDiff\w*' Mathlib (exists_contDiff_support_eq_eq_one_iff, exists_contMDiffMap_one_nhds_of_subset_interior); grep setIntegral_congr_fun₀, restrict_congr_set`
- `python3 -I scans of dag.json (354 nodes): accepted nodes; lean_statement patterns VanishesOn / restrictDomain / covectorEuclideanNorm with • / ContDiff cutoffs / '.support ⊆' with Disjoint; reuse candidates br_la_abs_apply_le_mul_mass, fiw_ims_sc_converges_zero_small, lpf_rectifiable_support_null, br_weightedTangent_congr (byte-identical types); existing cross-branch reuse edges`
- `git show <commit>:GMT/Ch06/Submission.lean | grep -A8 'theorem Submission.<name>' for d771ac3a (br_la_abs_apply_le_mul_mass), 49ba437c (fiw_ims_sc_converges_zero_small), b0d12af0 (lpf_rectifiable_support_null), def607d8 (br_weightedTangent_congr)`
- `git log --all --oneline -S fiw_tb_ext_ (1141 refs, no match); grep -rl fiw_tb_ext_ .humanize/math-wiki (no match)`
- `read /runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py (_decompose, _solve_children, _existing_lean_name_problem, _install_parent_supplied_child_handoff, accepted-child overlay) and store.py (ensure)`
- `python3 -I /tmp/extdecomp_tools/gen.py (verifier/gmt-compare.py child_modules contract mode + lean_contract.validate_lean_statement); lake env lean /tmp/extdecomp/AllChallenges.lean (all 12 statements elaborate)`
- `lake env lean /tmp/extdecomp/Assembly.lean (#print axioms assembly: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/extdecomp/Small.lean, /tmp/extdecomp/Big.lean, /tmp/extdecomp/E2E.lean (trial proofs of all 8 new children; Submission-style end-to-end with exact Submission.X checks)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-mass-estimate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1-converges-small-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-tangent-locality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/extdecomp/AllChallenges.lean`
- `/tmp/extdecomp/Assembly.lean`
- `/tmp/extdecomp/Small.lean`
- `/tmp/extdecomp/Big.lean`
- `/tmp/extdecomp/E2E.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) is byte-identical to the workspace build used for checking. It holds the frozen Ch06 contract: IsRectifiableTriple, tauAction, IsIntegerMultiplicity.

SimonGMT supplies the current/test-form API used in every child:
- TestFormOn as a submodule, with pointwise operations;
- GeometricCurrentOn with sequential continuity at 0, GeometricCurrentOn.ext, boundary_apply and tsupport_exteriorDerivative_subset;
- massAdmissibleOn, massOn, mass and le_massOn;
- testFormOnInclusion and restrictDomain_apply;
- VanishesOn, zeroRegion and support;
- CountablyRectifiable.mono.
There is no covectorEuclideanNorm smul lemma (new child norm_smul) and no converse of vanish_off_support (new child support_subset).

Mathlib supplies:
- exists_compact_between and exists_contDiff_support_eq_eq_one_iff (cutoff);
- ContDiff.smul and tsupport_smul_subset_left/right (smul_testform);
- ae_eq_set, Measure.restrict_congr_set and setIntegral_congr_fun₀ (im_extend).

dag.json has four accepted declarations whose frozen types are byte-identical to what the supplied proof cites. Each was verified at its candidate commit:
- br_la_abs_apply_le_mul_mass (d771ac3a);
- fiw_ims_sc_converges_zero_small (49ba437c);
- lpf_rectifiable_support_null (b0d12af0; the support-null fact without MF);
- br_weightedTangent_congr (def607d8).
They are reused as children. The runtime maps them to the accepted nodes, and cross-branch reuse of accepted nodes is established in this DAG.

Kernel checks:
- all 12 child types elaborate in the comparator's exact challenge scope;
- the parent type follows from the 8 new child types plus vanish_off_support, with axioms [propext, Classical.choice, Quot.sound];
- each new child has a trial Lean proof from exactly its declared siblings.
