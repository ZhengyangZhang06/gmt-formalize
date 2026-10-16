# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1.cycle_competitor-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (the competitor Z := S + (push Y)|_U: it is integer multiplicity, ∂Z = ∂S, spt(Z − S) ⊆ K_π, and minimality gives M_{B_G}(S) ≤ M_{B_G}(Z)). Here the push-forward π_#Y is replaced by an arbitrary integer multiplicity cycle X and K_π = π(spt Y) by any compact K with spt X ⊆ K ⊆ A ∩ W. The parent applies it with X = π_#Y, K = π(spt Y) and W = B_G(0). This is Simon's inequality 7.2.4 (9) (chapter-07.txt lines 237–243): since T_j is minimizing, ∂(X + ∂R̃_j) = 0 and spt(X + ∂R̃_j) ⊆ W_σ, M_W(T_j + X + ∂R̃_j) ≥ M_W(T_j).

Siblings used:
- im_calculus (c) [IMC-c]: if U' is open and A, B ∈ 𝒟_n(U') are integer multiplicity, so is A − B.
- restrict_domain_im [RD]: if V ⊆ U', V is open and T ∈ 𝒟_n(U') is integer multiplicity, then T.restrictDomain (V ⊆ U') is integer multiplicity in V.
- vanish_off_support [V]: T(ω) = 0 whenever tsupport ω is disjoint from spt T.
- support_of_vanishing [SV]: if U' is open, K ⊆ U' is compact and F ∈ 𝒟_n(U') satisfies F(ω) = 0 for every ω whose tsupport is disjoint from K, then spt F ⊆ K and spt F is compact.

Notation. ι := testFormOnInclusion (U ⊆ ℝ^P) keeps the underlying form, so X|_U(ω) = X(ιω) and tsupport(ιω) = tsupport ω. Values of differences are differences of values, (A − B)(ω) = A(ω) − B(ω), and 0(ω) = 0. Currents that agree on every test form are equal (GeometricCurrentOn.ext). Put Z := S − (0 − X|_U), so Z(ω) = S(ω) − (0 − X(ιω)) = S(ω) + X(ιω).

1. (Z is integer multiplicity.) S is integer multiplicity by the first conjunct of IsMinimizingIn S A. X|_U is integer multiplicity by RD (U ⊆ ℝ^P, U open). By IMC-c, X|_U − X|_U is integer multiplicity. It takes the value X|_U(ω) − X|_U(ω) = 0 on every ω, so it equals 0, and therefore 0 ∈ 𝒟_n(U) is integer multiplicity. By IMC-c twice, 0 − X|_U and Z = S − (0 − X|_U) are integer multiplicity.

2. (∂Z = ∂S.) The degree is m + 1, so SameBoundary Z S is the equation Z.boundary = S.boundary. Let ω ∈ 𝒟ᵐ(U). Then ∂Z(ω) = Z(dω) = S(dω) − (0 − X(ι(dω))). As test forms on ℝ^P, ι(dω) = d(ιω), since both have underlying form dω. Hence X(ι(dω)) = X(d(ιω)) = ∂X(ιω) = 0, because ∂X = 0. So ∂Z(ω) = S(dω) = ∂S(ω), and Z.boundary = S.boundary by ext.

3. (spt(Z − S) is compact and contained in A ∩ W.) First, K ⊆ A ∩ W ⊆ W ⊆ closure(W) ⊆ U. Let ω ∈ 𝒟ⁿ(U) with tsupport ω disjoint from K. Then (Z − S)(ω) = (S(ω) − (0 − X(ιω))) − S(ω) = X(ιω). Since tsupport(ιω) = tsupport ω is disjoint from K ⊇ spt X, V gives X(ιω) = 0. So Z − S vanishes on every form of 𝒟ⁿ(U) whose support misses K. SV (U open, K compact, K ⊆ U) gives spt(Z − S) ⊆ K and spt(Z − S) compact. Hence spt(Z − S) ⊆ K ⊆ A ∩ W.

4. (Minimality.) Apply the second conjunct of IsMinimizingIn S A to the open set W (W ⊂⊂ U) and the current Z. Z is integer multiplicity (step 1), SameBoundary Z S holds (step 2), and spt(Z − S) is compact and contained in A ∩ W (step 3). So M_W(S) ≤ M_W(Z) = M_W(S − (0 − X|_U)). ∎

Checked Lean realization (not part of the mathematical argument). The following single declaration was compiled in a scratch copy (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630, import GMT.Ch07.Submission at b4d606d, scope of the frozen contract), with the four siblings declared as Submission.* axioms of their exact frozen types; #print axioms lists only propext, Classical.choice, Quot.sound and those four siblings.

theorem Submission.dtc_bc_lc_rc_cycle_competitor : ∀ (P m : ℕ) (U A W K : Set (Euclid P)) (S : GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsOpen U → IsMinimizingIn S A → IsOpen W → CompactlyContained W U → IsIntegerMultiplicity X → X.boundary = 0 → IsCompact K → X.support ⊆ K → K ⊆ A ∩ W → S.massOn W ≤ (S - (0 - X.restrictDomain (subset_univ U))).massOn W := by
  have hIM := Submission.cmc_imRep_locality_restrict_sub
  have hRD := Submission.dtc_restrictDomain_isIntegerMultiplicity
  have hV := Submission.dtc_vanish_off_support
  have hSV := Submission.rsd_cmr_support_subset_of_vanish
  intro P m U A W K S X hU hmin hW hWU hXim hXbd hK hXK hKAW
  have hXUim : IsIntegerMultiplicity (X.restrictDomain (subset_univ U)) :=
    hRD P (m + 1) univ U (subset_univ U) X hU hXim
  have h0im : IsIntegerMultiplicity (0 : GeometricCurrentOn U (m + 1)) := by
    have h := hIM.2.2.1 P (m + 1) U _ _ hU hXUim hXUim
    have h' : X.restrictDomain (subset_univ U) - X.restrictDomain (subset_univ U) = 0 := by
      ext ω
      show X.restrictDomain (subset_univ U) ω - X.restrictDomain (subset_univ U) ω = 0
      ring
    rwa [h'] at h
  have hZim : IsIntegerMultiplicity (S - (0 - X.restrictDomain (subset_univ U))) :=
    hIM.2.2.1 P (m + 1) U S _ hU hmin.1 (hIM.2.2.1 P (m + 1) U 0 _ hU h0im hXUim)
  have hbd : SameBoundary (S - (0 - X.restrictDomain (subset_univ U))) S := by
    show (S - (0 - X.restrictDomain (subset_univ U))).boundary = S.boundary
    ext ω
    have h2 : X (exteriorDerivativeTestOn univ m (testFormOnInclusion (subset_univ U) m ω)) = 0 := by
      have := congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) m =>
        T (testFormOnInclusion (subset_univ U) m ω)) hXbd
      exact this
    show S (exteriorDerivativeTestOn U m ω) - ((0 : GeometricCurrentOn U (m + 1))
        (exteriorDerivativeTestOn U m ω) - X (exteriorDerivativeTestOn univ m
          (testFormOnInclusion (subset_univ U) m ω))) = S (exteriorDerivativeTestOn U m ω)
    rw [h2, GeometricCurrentOn.zero_apply]
    ring
  have hKU : K ⊆ U := fun x hx => hWU.2 (subset_closure (hKAW hx).2)
  have hspt := hSV P (m + 1) U K ((S - (0 - X.restrictDomain (subset_univ U))) - S) hU hK hKU
    (fun ω hω => by
      have hX0 : X (testFormOnInclusion (subset_univ U) (m + 1) ω) = 0 :=
        hV P (m + 1) univ X _ (by
          rw [testFormOnInclusion_coe]
          exact hω.mono_right hXK)
      show (S ω - ((0 : GeometricCurrentOn U (m + 1)) ω -
        X (testFormOnInclusion (subset_univ U) (m + 1) ω))) - S ω = 0
      rw [hX0, GeometricCurrentOn.zero_apply]
      ring)
  exact hmin.2 W _ hW hWU hZim hbd hspt.2 (hspt.1.trans hKAW)

## Key steps

1. Z := S − (0 − X|_U) is integer multiplicity: restrict_domain_im for X|_U, 0 = X|_U − X|_U, and im_calculus (c).
2. ∂Z = ∂S, because ι commutes with d and ∂X = 0.
3. Z − S = X|_U vanishes on forms supported off K ⊇ spt X (vanish_off_support), so spt(Z − S) is a compact subset of K ⊆ A ∩ W (support_of_vanishing).
4. Minimality of S in A, with the open set W ⊂⊂ U and the competitor Z, gives M_W(S) ≤ M_W(Z).

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
