# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.piece_pushforward-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.piece_pushforward-a1.unit_piece_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent steps 7, 8 and 12, and the integrability of f on C′ in parent step 11, stated for an arbitrary multiplicity-one triple (M, 1, η) instead of (C′, 1, ξ′): "R′ := (C′, θ ≡ 1, ξ′) is an IMRep in ℝ^P: C′ is Borel …; C′ is countably m-rectifiable …; θ ≡ 1 is measurable and positive on C′; ∫_{C′∩K} θ dH^m ≤ H^m(C′) < ∞ for every compact K …; ξ′ is a.e.-strongly measurable for H^m⌞C′ …; and for every y ∈ C′ … HasApproximateTangentSpaceAt m C′ y Q′(y) and ξ′(y) a unit orientation of Q′(y)" (step 7); "So R′ represents D, and D is integer multiplicity" (step 8); "D(ω) = ∫_{C′} f dH^m ≤ … ≤ H^m(C′ ∩ W′) … Taking the supremum over admissible ω: M_{W′}(D) ≤ H^m(Φ(N ∩ W) ∩ W′)" (step 12). Book: Simon 6.2.2 ([[M]](ω) = ∫_M ⟨ω(x), ξ(x)⟩ dHⁿ, chapter-06.txt line 203), Definition 6.3.1 with θ ≡ 1 (chapter-06.txt lines 733–753) and the inequality "≤" of Remark 6.3.2(3) (M_W(T) = ∫_{M∩W} θ dHⁿ, lines 761–766). The three sub-steps are the accepted sibling declarations
 - imrep_current (Submission.dtc_imrep_current): every IMRep R of U defines a current T ∈ 𝒟_n(U) with R.Represents T. This is the content of parent step 8, which obtained it from pushforward_current with φ = id;
 - action_integrable (Submission.regcomp_rim_action_integrable): for an IMRep R = (M, θ, ξ) and ω ∈ 𝒟ⁿ(U), x ↦ θ(x)·ξ(x)(ω(x)) is Hⁿ⌞M-integrable. This is the parent's bound |f| ≤ |ω| ≤ c_ω on C′ in step 11, for general θ;
 - mass_le_measure (Submission.dor_ims_massOn_le_measure): if R represents T then M_W(T) ≤ μ_R(W) for every set W. This is the parent's step-12 argument (pointwise bound by unit-orientation duality, then supremum over admissible ω), for general θ.

Notation. H^m = μHE[m]. For an IMRep R = (M, θ, ξ) of U, R.action ω = ∫_M (θ(x) : ℝ)·ξ(x)(ω(x)) dH^m(x), R.Represents T means T(ω) = R.action ω for every ω ∈ 𝒟^m(U), and μ_R := R.measure = (H^m⌞M).withDensity (x ↦ (θ(x) : [0, ∞])).

Proof.
1. (The multiplicity-one triple.) Define R : IMRep ℝ^P m with carrier M, multiplicity θ the constant function with value the natural number 1, and orientation η. The structure fields hold:
 - M is measurable: hypothesis;
 - M ⊆ ℝ^P: trivial;
 - M is countably m-rectifiable: hypothesis;
 - θ is measurable (a constant function) and θ(y) = 1 > 0 for every y ∈ M;
 - for every compact K (K ⊆ ℝ^P holds trivially), ∫⁻_{M∩K} θ dH^m = ∫⁻_{M∩K} 1 dH^m = 1·H^m(M ∩ K) = H^m(M ∩ K) < ∞ (lower integral of a constant over a set, setLIntegral_const, and the hypothesis on compact sets);
 - η is a.e.-strongly measurable for H^m⌞M: hypothesis;
 - for H^m⌞M-a.e. y there is Q with HasApproximateTangentSpaceAt m M y Q and IsUnitOrientationOf (η y) Q: hypothesis.
2. (The current.) By imrep_current applied to R (with U = ℝ^P, n = m) there is D ∈ 𝒟_m(ℝ^P) with R.Represents D, i.e. D(ω) = R.action ω for every ω ∈ 𝒟^m(ℝ^P). In particular D is integer multiplicity: IsIntegerMultiplicity D is witnessed by R. This is the first conclusion.
3. (Integrability and the formula.) Let ω ∈ 𝒟^m(ℝ^P). By action_integrable applied to R and ω, the function y ↦ (θ(y) : ℝ)·η(y)(ω(y)) is H^m⌞M-integrable. Since (θ(y) : ℝ) = 1 for every y, this function is y ↦ η(y)(ω(y)), which is therefore H^m⌞M-integrable. By step 2 and the definition of the action, D(ω) = R.action ω = ∫_M 1·η(y)(ω(y)) dH^m(y) = ∫_M η(y)(ω(y)) dH^m(y). This is the second conclusion.
4. (Mass bound.) Let W′ ⊆ ℝ^P be an arbitrary set. Since R represents D (step 2), mass_le_measure gives M_{W′}(D) ≤ μ_R(W′). As θ ≡ 1, the density x ↦ (θ(x) : [0, ∞]) is the constant function 1, so μ_R = (H^m⌞M).withDensity 1 = H^m⌞M (withDensity_one). As M is measurable, (H^m⌞M)(W′) = H^m(W′ ∩ M) for every set W′, measurable or not (Measure.restrict_apply′, which requires only the measurability of M), and W′ ∩ M = M ∩ W′. Hence M_{W′}(D) ≤ H^m(M ∩ W′). This is the third conclusion. ∎

Lean note. The following proof was compiled against the actual accepted declarations (textual union of the accepted candidate commits 642d7450f79f, f1339f96a29c and fae4fd1e831d; Lean v4.35.0-rc3, Mathlib 25730c7c; #print axioms: propext, Classical.choice, Quot.sound):
  intro P m M η hM hrect hfin hη horient
  let R : IMRep (univ : Set (Euclid P)) m :=
    { carrier := M
      mult := fun _ => 1
      orient := η
      measurableSet_carrier := hM
      carrier_subset := subset_univ M
      rectifiable := hrect
      measurable_mult := measurable_const
      mult_pos := fun _ _ => Nat.one_pos
      locallyIntegrable_mult := fun K hK _ => by
        simp only [Nat.cast_one, setLIntegral_const, one_mul]
        exact hfin K hK
      aestronglyMeasurable_orient := hη
      orients := horient }
  obtain ⟨D, hD⟩ := Submission.dtc_imrep_current P m univ R
  refine ⟨D, ⟨R, hD⟩, fun ω => ?_, fun W' => ?_⟩
  · have hi := Submission.regcomp_rim_action_integrable P m univ R ω
    simp only [R, Nat.cast_one, one_mul] at hi
    refine ⟨hi, ?_⟩
    rw [hD ω]
    simp only [IMRep.action, R, Nat.cast_one, one_mul]
  · have hm := Submission.dor_ims_massOn_le_measure P m univ D R hD W'
    have hmeas : R.measure = μHE[m].restrict M := by
      simp only [IMRep.measure, R, Nat.cast_one]
      exact withDensity_one
    rw [hmeas, Measure.restrict_apply' hM, inter_comm] at hm
    exact hm

## Key steps

1. R := (M, θ ≡ 1, η) is an IMRep of ℝ^P: every field is a hypothesis, local integrability being ∫⁻_{M∩K} 1 dH^m = H^m(M ∩ K) < ∞.
2. imrep_current gives D with R.Represents D; hence D is integer multiplicity.
3. action_integrable with θ ≡ 1 gives integrability of η(·)(ω(·)) on M, and D(ω) = R.action ω = ∫_M η(ω) dH^m.
4. mass_le_measure gives M_{W′}(D) ≤ μ_R(W′) = (H^m⌞M)(W′) = H^m(M ∩ W′) (withDensity_one; Measure.restrict_apply′ with M Borel).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum of snapshot vs workspace GMT/Ch07/{Contract,Submission}.lean and of 8 cited Mathlib files (snapshot vs .lake/packages/mathlib)`
- `rg -n 'theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part|theorem withDensity_one|theorem restrict_apply'' |theorem setLIntegral_const|theorem setLIntegral_one|lemma enorm_of_nonneg|lemma enorm_mul|lemma Homeomorph.measurableEmbedding' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul|theorem integral_image_eq_integral_abs_det_fderiv_smul' <snapshot>/mathlib/Mathlib (same-dimension Lebesgue Jacobian formula only)`
- `grep -n 'continuous_compContinuousLinearMapCLM|def compContinuousLinearMapCLM|to_rightInverse|norm_fderiv_le_of_lipschitz|theorem setLIntegral_mono|theorem ContinuousOn.aestronglyMeasurable|pseudoMetrizableSpace' in Mathlib Alternating/Basic, Alternating/Topology, Antilipschitz, FDeriv/Basic, Lebesgue/Basic, IntegrableOn, Metrizable/Basic`
- `rg -n 'structure IMRep|def IMRep.measure|def IsIntegerMultiplicity|def IsEmbeddedSubmanifold|def IsOrientation' <snapshot>/project/GMT/Ch07/Contract.lean; rg -n 'codim1_ac_pp_' <snapshot>/project (no match); rg -c CountablyRectifiable <snapshot>/mathlib/Mathlib (no match); rg -n IsSimonSubmanifold <snapshot>/project (GMT/Ch02 only)`
- `rg -n 'theorem countablyRectifiable_of_isSimonSubmanifold|theorem measurableSet_of_isSimonSubmanifold|def IsSimonSubmanifold|def IsProperOnInto|theorem CountablyRectifiable.mono' SimonGMT; sed SimonGMT Chapter06/{Forms,Currents,Mass}.lean (IsTestForm, TestFormOn, GeometricCurrentOn, covectorEuclideanNorm, massAdmissibleOn, massOn)`
- `python scans of dag.json (1514 nodes): accepted statements mentioning massOn+IMRep, ∃ current + Represents, Integrable + orient, IsEmbeddedSubmanifold + MeasurableSet/CountablyRectifiable; lean_name uniqueness and status of dtc_imrep_current, regcomp_rim_action_integrable, dor_ims_massOn_le_measure, dor_ims_unitOrientation_dual, dor_ims_action_eq_integral; duplicates rsd_cmr_imrep_represents_exists, rsd_cmr_ic_action_integrable, regcomp_imrep_massOn_le_measure, rsd_mw_massOn_le_measure, dimred_rpd_embedded_locally_closed, dpfir_ii_countablyRectifiable_image_of_lipschitz, cmcdt_ims_imrep_of_int_density considered`
- `git show <candidate>:GMT/Ch07/Submission.lean for 642d7450f79f, f1339f96a29c, fae4fd1e831d, c2e1da27351f, 9c8432cb0101, 863f6d9cf603, 3de784c0d8f0 (declaration present, type byte-identical, no extra imports); declarations added per candidate; git grep codim1_ac_pp_ over 2580 distinct ref tips (no match; control codim1_ac_perturbation_diffeo found)`
- `runtime.py: _decompose (max_depth 6), _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, _merge_candidate_history/_union_lean_conflicts, _reference_use_problem`
- `lean -DautoImplicit=false /tmp/pp-split/check/{Types,Child1,Child2,Child3,Assembly,AssemblyAx}.lean and /tmp/pp-split/full/{Full,FullAssembly}.lean`
- `book: chapter-03.txt 12–60 (3.1.1, Lemma 1.2 'if' part); chapter-06.txt 203 (2.2), 733–768 (3.1, 3.2(3)), 770–859 (3.3–3.9); chapter-02.txt 776–797 (3.4–3.5), 960–981 (4.11–4.13)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-686f3f40d6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f448992aee/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-imrep-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-restriction-integer-multipl-1450eb50b9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-mass-up-4048586780/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-action-188f3b5994/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/pp-split/check/Types.lean`
- `/tmp/pp-split/check/Child1.lean`
- `/tmp/pp-split/check/Child2.lean`
- `/tmp/pp-split/check/Child3.lean`
- `/tmp/pp-split/check/Assembly.lean`
- `/tmp/pp-split/check/AssemblyAx.lean`
- `/tmp/pp-split/full/Full.lean`
- `/tmp/pp-split/full/FullAssembly.lean`

Pins match.
- The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib.
- The snapshot and workspace GMT/Ch07/Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
- The cited Mathlib files are byte-identical between snapshot and workspace.
Library facts used by the split, all present in the snapshot Mathlib:
- Bochner/Basic.lean:486 integral_eq_lintegral_pos_part_sub_lintegral_neg_part (signed integral as a difference of positive and negative parts).
- WithDensity.lean:175 withDensity_one; Restrict.lean:111 restrict_apply' (needs only the measurability of the restricting set).
- Lebesgue/Basic.lean:121/124 setLIntegral_const and setLIntegral_one; :246 setLIntegral_mono.
- Normed/Group/Real.lean:95 Real.enorm_of_nonneg; Normed/Ring/Basic.lean:735 enorm_mul.
- BorelSpace/Basic.lean:567 Homeomorph.measurableEmbedding.
- Alternating/Basic.lean:437 continuous_compContinuousLinearMapCLM; Alternating/Topology.lean:281 compContinuousLinearMapCLM (simps apply).
- Antilipschitz.lean:137 AntilipschitzWith.to_rightInverse; FDeriv/Basic.lean:947 norm_fderiv_le_of_lipschitz.
- IntegrableOn.lean:791 ContinuousOn.aestronglyMeasurable, which needs PseudoMetrizableSpace. The instance is not found for MultiVector P m, so it is supplied explicitly as PseudoEMetricSpace.pseudoMetrizableSpace, the workaround used in accepted branches.
What the libraries lack:
- Mathlib's Jacobian.lean has only the same-dimension Lebesgue change of variables. Nothing transfers signed integrands through an H^m area formula on submanifolds, hence the new child signed_area_transfer.
- SimonGMT SubmanifoldCover.lean proves measurableSet_of_isSimonSubmanifold and countablyRectifiable_of_isSimonSubmanifold for IsSimonSubmanifold (Submanifold.lean, with IsProperOnInto). The contract's IsEmbeddedSubmanifold differs only by the smoothness-order cast and the order of the properness hypotheses, hence the new child embedded_rectifiable.
- Snapshot Mathlib has no CountablyRectifiable (no match); the snapshot project has no codim1_ac_pp_ names (no match).
DAG.
- Accepted, reusable, byte-identical: dtc_imrep_current (IMRep ⇒ represented current), regcomp_rim_action_integrable (integrability of θ⟨ω, ξ⟩ on the carrier), dor_ims_massOn_le_measure (M_W(T) ≤ μ_R(W) for all W), and its prerequisites dor_ims_unitOrientation_dual and dor_ims_action_eq_integral.
- Each maps to a unique accepted node whose candidate commit contains the declaration and adds no imports.
- With these, the new child unit_piece_current (Simon 6.2.2/6.3.1/6.3.2(3) with θ ≡ 1) has a short proof.
- The node's unaccepted prerequisites (submanifold_approx_tangent, submanifold_area) cannot be shared by children, so the geometric glue stays in this node. image_submanifold was accepted only during this session.
Lean.
- Types.lean elaborates all 8 child types.
- Child1–3 and Full.lean (real accepted declarations, textual union of their candidate commits) prove the 3 new children with axioms propext, Classical.choice and Quot.sound.
- FullAssembly.lean proves the selected frozen type from the children and the 4 used prerequisite types (as axioms).
- All of these exit 0.
