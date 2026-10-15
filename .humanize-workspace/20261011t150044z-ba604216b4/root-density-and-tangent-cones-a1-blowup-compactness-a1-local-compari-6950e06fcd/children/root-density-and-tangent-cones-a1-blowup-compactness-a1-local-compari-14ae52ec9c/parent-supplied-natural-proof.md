# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1.ambient_restriction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (Q := S⌞B_G as a current in ℝ^P, with (Q1) and (Q2)), stated for an arbitrary open W ⊂⊂ U. The parent applies it with W = B_G(0), whose closure closedBall(0, G) is compact and contained in U. It is the supplied proof's own device for applying the push-forward, which is defined for currents in ℝ^P, to the part of S inside B_G. Simon states 7.2.4 and Remark 7.2.5(2) at chapter-07.txt lines 157–175 and leaves the modification of the proof of 2.4 to minimizers in submanifolds N_j to the reader; this restriction step is not printed there.

Siblings used:
- im_calculus (b) [IMC-b]: if U' is open, R' is an IMRep of U' and E is Borel, there are a current A ∈ 𝒟_n(U') and an IMRep of U' representing A with carrier R'.carrier ∩ E and the same multiplicity and orientation.
- mass_eq_measure [M]: if U' and O are open, O ⊆ U' and R' represents T in U', then M_O(T) = R'.measure(O).
- vanish_off_support [V]: T(ω) = 0 whenever tsupport ω is disjoint from spt T.
- support_of_vanishing [SV]: if U' is open, K ⊆ U' is compact and F ∈ 𝒟_n(U') satisfies F(ω) = 0 for every ω whose tsupport is disjoint from K, then spt F ⊆ K and spt F is compact.

Notation. Hⁿ := μHE[n]. For an IMRep R' = (M', θ', ξ') and a form ω, R'.action ω = ∫_{M'} θ'(x)·ξ'(x)(ω(x)) dHⁿ(x), and R'.Represents T means T(ω) = R'.action ω for every test form ω of the domain of T. R'.measure = θ'Hⁿ⌞M' (withDensity), so R'.measure(E) = ∫_{M'∩E} θ' dHⁿ for Borel E. spt T = U' ∖ Z_T, where the zero region Z_T is open (isOpen_zeroRegion).

1. (The triple (M ∩ W, θ, ξ) in U.) W is open, hence Borel. IMC-b with (U, R, E := W) gives an IMRep R' of U with carrier M ∩ W, multiplicity θ and orientation ξ. Its fields give: M ∩ W is countably n-rectifiable; ξ is Hⁿ⌞(M ∩ W)-a.e. strongly measurable; for Hⁿ⌞(M ∩ W)-a.e. x there is a subspace Q_x with HasApproximateTangentSpaceAt n (M ∩ W) x Q_x and IsUnitOrientationOf (ξ x) Q_x.

2. (The same triple in ℝ^P.) Define R₀ : IMRep univ n with carrier M ∩ W, multiplicity θ and orientation ξ. Its fields hold:
 (a) M ∩ W is Borel (M is Borel and W is open), and M ∩ W ⊆ ℝ^P.
 (b) Rectifiability, a.e. strong measurability of ξ and the orientation property hold by step 1. These fields refer only to the carrier M ∩ W and to θ, ξ, not to the domain.
 (c) θ is measurable, and θ(x) > 0 for x ∈ M ∩ W, since x ∈ M.
 (d) Local integrability in ℝ^P. Let K ⊆ ℝ^P be compact. Since (M ∩ W) ∩ K ⊆ M ∩ closure(W), ∫_{(M∩W)∩K} θ dHⁿ ≤ ∫_{M∩closure(W)} θ dHⁿ < ∞. The last bound is the local integrability of R in U, applied to the compact set closure(W) ⊆ U (lintegral_mono_set).

3. (The current Q.) IMC-b with (ℝ^P, R₀, E := ℝ^P) gives Q ∈ 𝒟_n(ℝ^P) and an IMRep R_Q of ℝ^P with R_Q.Represents Q, carrier (M ∩ W) ∩ ℝ^P = M ∩ W, multiplicity θ and orientation ξ. Thus Q(η) = ∫_{M∩W} θ ξ(η) dHⁿ for every η ∈ 𝒟ⁿ(ℝ^P).

4. (Q1) Let ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ W. The form ιω has the same underlying form as ω (testFormOnInclusion_coe), so Q(ιω) = ∫_{M∩W} θ ξ(ω) dHⁿ. Also S(ω) = ∫_M θ ξ(ω) dHⁿ, because R represents S. For x ∈ M ∖ (M ∩ W) we have x ∉ W ⊇ tsupport ω, so ω(x) = 0 (image_eq_zero_of_notMem_tsupport) and the integrand θ(x)·ξ(x)(0) = 0. As M is measurable and M ∩ W ⊆ M, the integral over M equals the integral over M ∩ W (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero). Hence Q(ιω) = S(ω).

5. (Hⁿ(M ∖ spt S) = 0.)
 (a) O := U ∖ spt S equals U ∩ Z_S, because spt S = U ∖ Z_S. So O is open, and O ⊆ U.
 (b) M_O(S) = 0. Every admissible form ω for M_O has tsupport ω ⊆ O, and O is disjoint from spt S, so S(ω) = 0 by V. Every element ofReal(S(ω)) of the set whose supremum is M_O(S) is therefore 0.
 (c) By M (U and O open, O ⊆ U, R represents S): R.measure(O) = M_O(S) = 0, that is, ∫_{O∩M} θ dHⁿ = 0 (withDensity_apply, Measure.restrict_restrict).
 (d) θ ≥ 1 on M, so Hⁿ(O ∩ M) = ∫_{O∩M} 1 dHⁿ ≤ ∫_{O∩M} θ dHⁿ = 0.
 (e) M ⊆ U, so M ∖ spt S ⊆ O ∩ M. Hence Hⁿ(M ∖ spt S) = 0.

6. (Q2) Put K := closure(W) ∩ spt S.
 (a) K is compact. Since closure(W) ⊆ U, K = closure(W) ∩ (ℝ^P ∖ Z_S), the intersection of the compact set closure(W) with a closed set.
 (b) Q vanishes off K. Let η ∈ 𝒟ⁿ(ℝ^P) with tsupport η disjoint from K. By step 5, (M ∩ W) ∖ spt S ⊆ M ∖ spt S is Hⁿ-null, so Hⁿ-a.e. x ∈ M ∩ W lies in spt S. For such x, x ∈ W ⊆ closure(W), so x ∈ K. Then x ∉ tsupport η, so η(x) = 0 and θ(x)·ξ(x)(η(x)) = 0. Thus the integrand of Q(η) = ∫_{M∩W} θ ξ(η) dHⁿ vanishes Hⁿ⌞(M ∩ W)-a.e., and Q(η) = 0 (integral_eq_zero_of_ae).
 (c) SV with (ℝ^P, K, Q) (ℝ^P is open, K is compact, K ⊆ ℝ^P) gives spt Q ⊆ K = closure(W) ∩ spt S and spt Q compact.

7. Steps 3, 4 and 6 give Q and R_Q with all the stated properties. ∎

Checked Lean realization (not part of the mathematical argument). The following single declaration was compiled in a scratch copy (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630, import GMT.Ch07.Submission at b4d606d, scope of the frozen contract), with the four siblings declared as Submission.* axioms of their exact frozen types; #print axioms lists only propext, Classical.choice, Quot.sound and those four siblings.

theorem Submission.dtc_bc_lc_rc_ambient_restriction : ∀ (P n : ℕ) (U W : Set (Euclid P)) (S : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → IsOpen W → CompactlyContained W U → R.Represents S → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) n) (RQ : IMRep (univ : Set (Euclid P)) n), RQ.Represents Q ∧ RQ.carrier = R.carrier ∩ W ∧ RQ.mult = R.mult ∧ RQ.orient = R.orient ∧ (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → Q (testFormOnInclusion (subset_univ U) n ω) = S ω) ∧ Q.support ⊆ closure W ∩ S.support ∧ IsCompact Q.support := by
  have hIM := Submission.cmc_imRep_locality_restrict_sub
  have hM := Submission.dtc_mass_eq_measure
  have hV := Submission.dtc_vanish_off_support
  have hSV := Submission.rsd_cmr_support_subset_of_vanish
  intro P n U W S R hU hW hWU hR
  obtain ⟨A₀, R', -, hR'c, hR'm, hR'o⟩ := hIM.2.1 P n U R W hU hW.measurableSet
  have hrect : CountablyRectifiable n (R.carrier ∩ W) := hR'c ▸ R'.rectifiable
  have hasm : AEStronglyMeasurable R.orient (μHE[n].restrict (R.carrier ∩ W)) := by
    rw [← hR'c, ← hR'o]; exact R'.aestronglyMeasurable_orient
  have hor : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (R.carrier ∩ W) x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    rw [← hR'c, ← hR'o]; exact R'.orients
  let R₀ : IMRep (univ : Set (Euclid P)) n :=
    { carrier := R.carrier ∩ W
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := R.measurableSet_carrier.inter hW.measurableSet
      carrier_subset := subset_univ _
      rectifiable := hrect
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      locallyIntegrable_mult := fun K _ _ => by
        apply ne_top_of_le_ne_top (R.locallyIntegrable_mult (closure W) hWU.1 hWU.2)
        apply lintegral_mono_set
        intro x hx
        exact ⟨hx.1.1, subset_closure hx.1.2⟩
      aestronglyMeasurable_orient := hasm
      orients := hor }
  obtain ⟨Q, RQ, hRQ, hRQc, hRQm, hRQo⟩ := hIM.2.1 P n univ R₀ univ isOpen_univ MeasurableSet.univ
  have hRQc' : RQ.carrier = R.carrier ∩ W := by rw [hRQc]; exact inter_univ _
  -- the null set M \ spt S
  have hnull : μHE[n] (R.carrier \ S.support) = 0 := by
    have hopen : IsOpen (U \ S.support) := by
      have : U \ S.support = U ∩ S.zeroRegion := by
        ext x
        simp only [GeometricCurrentOn.support, Set.mem_sdiff, mem_inter_iff, not_and, not_not]
        constructor
        · intro h; exact ⟨h.1, h.2 h.1⟩
        · intro h; exact ⟨h.1, fun _ => h.2⟩
      rw [this]
      exact hU.inter S.isOpen_zeroRegion
    have hmass : S.massOn (U \ S.support) = 0 := by
      apply le_zero_iff.mp
      apply sSup_le
      rintro r ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (S ω) ≤ 0
      rw [hV P n U S ω (by
        rw [← Set.subset_compl_iff_disjoint_right]
        exact hω.1.trans (fun x hx => hx.2)), ENNReal.ofReal_zero]
    have hmeas : R.measure (U \ S.support) = 0 := by
      rw [← hM P n U (U \ S.support) S R hU hopen sdiff_subset hR, hmass]
    unfold IMRep.measure at hmeas
    rw [withDensity_apply _ hopen.measurableSet, Measure.restrict_restrict hopen.measurableSet] at hmeas
    have hle : μHE[n] ((U \ S.support) ∩ R.carrier) ≤
        ∫⁻ x in (U \ S.support) ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
      calc μHE[n] ((U \ S.support) ∩ R.carrier)
          = ∫⁻ x in (U \ S.support) ∩ R.carrier, (1 : ℝ≥0∞) ∂μHE[n] := by
            rw [setLIntegral_const, one_mul]
        _ ≤ ∫⁻ x in (U \ S.support) ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
            apply setLIntegral_mono' (hopen.measurableSet.inter R.measurableSet_carrier)
            intro x hx
            have := R.mult_pos x hx.2
            exact_mod_cast this
    have h0 : μHE[n] ((U \ S.support) ∩ R.carrier) = 0 := le_zero_iff.mp (hmeas ▸ hle)
    apply measure_mono_null _ h0
    intro x hx
    exact ⟨⟨R.carrier_subset hx.1, hx.2⟩, hx.1⟩
  refine ⟨Q, RQ, hRQ, hRQc', hRQm, hRQo, ?_, ?_⟩
  · -- (Q1)
    intro ω hω
    rw [hRQ, hR ω]
    unfold IMRep.action
    rw [hRQc', hRQm, hRQo, testFormOnInclusion_coe]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier inter_subset_left
    intro x hx
    have : (ω : DifferentialForm (Euclid P) n) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx.2 ⟨hx.1, hω h⟩)
    simp [this]
  · -- (Q2)
    have hKcpt : IsCompact (closure W ∩ S.support) := by
      have : closure W ∩ S.support = closure W ∩ (S.zeroRegion)ᶜ := by
        ext x
        simp only [GeometricCurrentOn.support, mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
        constructor
        · intro h; exact ⟨h.1, h.2.2⟩
        · intro h; exact ⟨h.1, hWU.2 h.1, h.2⟩
      rw [this]
      exact hWU.1.inter_right S.isOpen_zeroRegion.isClosed_compl
    exact hSV P n univ (closure W ∩ S.support) Q isOpen_univ hKcpt (subset_univ _) (fun ω hω => by
      rw [hRQ ω]
      unfold IMRep.action
      rw [hRQc', hRQm, hRQo]
      apply integral_eq_zero_of_ae
      have hn' : μHE[n] ((R.carrier ∩ W) \ S.support) = 0 :=
        measure_mono_null (sdiff_subset_sdiff_left inter_subset_left) hnull
      have hae : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), x ∈ S.support := by
        rw [ae_restrict_iff' (R.measurableSet_carrier.inter hW.measurableSet)]
        rw [ae_iff]
        apply measure_mono_null _ hn'
        intro x hx
        simp only [Set.mem_ofPred_eq, not_imp] at hx
        exact ⟨hx.1, hx.2⟩
      filter_upwards [hae, ae_restrict_mem (R.measurableSet_carrier.inter hW.measurableSet)]
        with x hx hxM
      have : (ω : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h =>
          hω.ne_of_mem h ⟨subset_closure hxM.2, hx⟩ rfl)
      simp [this])

## Key steps

1. im_calculus (b) in U with E = W makes (M ∩ W, θ, ξ) an integer multiplicity triple. It is locally integrable in all of ℝ^P because M ∩ W lies in the compact set closure(W) ⊆ U, so im_calculus (b) in ℝ^P with E = ℝ^P gives Q with representation (M ∩ W, θ, ξ).
2. (Q1): a form supported in W vanishes on M ∖ W, so the integrals over M and over M ∩ W agree.
3. Hⁿ(M ∖ spt S) = 0, by vanish_off_support, mass_eq_measure and θ ≥ 1.
4. (Q2): Q vanishes on forms supported off the compact set closure(W) ∩ spt S, and support_of_vanishing gives the support inclusion and compactness.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c); ls local-references/123e8435b4a2469b/project/GMT (contracts and README of Ch01–Ch08 only); grep -rn 'pushforward' project/GMT (only the Ch08 varifold pushforwardMeasure)`
- `read simongmt Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, GeometricCurrentOn.massOn, mass := massOn U, massOn_mono, le_massOn), Chapter06/Currents.lean (GeometricCurrentOn, ext, Zero instance and zero_apply, exteriorDerivativeTestOn, boundary, boundary_apply), Chapter06/CurrentLocalEquality.lean (testFormOnInclusion, testFormOnInclusion_coe, restrictDomain, restrictDomain_apply, VanishesOn, zeroRegion, support, isOpen_zeroRegion)`
- `python3 -I scans of runs/20261011T150044Z-ba604216b4/dag.json: parent decomposition nodes/…-local-comparison-a1/decomposition-v1.json (sibling types and the five re-listed accepted children); accepted statements mentioning massOn/restrictDomain/support/IsMinimizingIn (found dtc_massOn_eq_of_agreeOn, dtc_extend_by_zero, lcmp_massOn_le_add_of_eval_eq, cmc_fcl_massOn_le_add, lcmp_massOn_le_of_vanish_off_compact, cmc_massOn_le_of_le_near_support); search for nodes stating the two new lemmas (none besides this node); dependency-inheritance pattern of testform_extension-a1 (decomposition-v1.json rationale)`
- `git show <candidate commit>:GMT/Ch07/Submission.lean for dtc_massOn_eq_of_agreeOn (0c79e2a), dtc_mass_eq_measure (bff81d3), dtc_vanish_off_support (44ef61f), cmc_imRep_locality_restrict_sub (2af75d6), dtc_restrictDomain_isIntegerMultiplicity (8f3bacb), rsd_cmr_support_subset_of_vanish (02c6122): whitespace-normalised type comparison, all IDENTICAL; accepted natural proofs copied from each node's parent-supplied-natural-proof.md`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') and child_modules(…, 'contract') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all eight child types; lake env lean /tmp/rcsplit/challenges/Challenge_<key>.lean (8 modules, only the expected sorry warning)`
- `lake env lean /tmp/rcsplit/lean/{Types,Children,Assembly,SubmissionForm}.lean with #print axioms (restr_proof, comp_proof, ret_assembly; leaf-form Submission.dtc_bc_lc_rc_ambient_restriction, Submission.dtc_bc_lc_rc_cycle_competitor, Submission.dtc_bc_lc_retraction_comparison)`
- `Mathlib names used at the pin: norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.of_dist_le_mul, closure_ball, closedBall_subset_ball, ContDiffOn.differentiableOn, integral_congr_ae, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, image_eq_zero_of_notMem_tsupport, withDensity_apply, withDensity_absolutelyContinuous, Measure.restrict_restrict, setLIntegral_const, setLIntegral_mono', lintegral_mono_set, ae_restrict_iff', integral_eq_zero_of_ae, measure_add_measure_compl, Measure.le_iff', IsCompact.image_of_continuousOn, Set.subset_compl_iff_disjoint_right`
- `grep for dtc_bc_lc_rc_ambient_restriction, dtc_bc_lc_rc_cycle_competitor and the prefix dtc_bc_lc_rc_ in dag.json (1223 nodes at the final check), nodes/, GMT/ and .lake/packages/simongmt (no match); dag.json lookup of dimred_mbl_lc_retraction_comparison (analogous node, not accepted) and dtc_approxTangent_of_null_diff (accepted)`
- `sed book/chapter-07.txt lines 157–262 (Simon 7.2.4 statement, Remark 7.2.5(2), proof steps (8)–(12); inequality (9) at lines 237–243)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-6950e06fcd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-tes-dd42d587af/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-mass-agree-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/rcsplit/lean/Types.lean`
- `/tmp/rcsplit/lean/Children.lean`
- `/tmp/rcsplit/lean/Assembly.lean`
- `/tmp/rcsplit/lean/SubmissionForm.lean`

The pinned snapshot holds only chapter contracts; the SimonGMT library supplies currents, boundary, massOn/mass, support/zeroRegion, restrictDomain and testFormOnInclusion, but no restriction of a current to a subset, no extension to ℝ^P with an explicit representation and no competitor lemma. No accepted or active DAG node states the two new lemmas, so they are new children with unique names. Six accepted declarations are reused with identical types: dtc_massOn_eq_of_agreeOn (new for this node, used in steps 6(a) and 6(d)) and the five already re-listed by the parent. In Lean, the two children are proved from their declared siblings, and the exact frozen type of this node follows from the two children plus its declared dependencies (pushforward, orientation_fixed, measure_subadditive, mass_eq_measure, vanish_off_support, im_calculus, support_of_vanishing) and mass_agree, using only propext, Classical.choice and Quot.sound.
