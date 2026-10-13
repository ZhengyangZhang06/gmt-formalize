# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.cutoff_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof: the definition Y(ω) := X(χω) and its sequential continuity via the finite mass of X.
- The parent's sub-steps 4(b)–(c) (coefficient norm versus operator norm, and uniform smallness of a null sequence) are exactly the reused sibling converges_small.
- Sub-step 4(a) is the reused sibling eval_bound.

Notation. |α| := covectorEuclideanNorm α. μ_X := (X.mass).toReal, a real number ≥ 0 (ENNReal.toReal_nonneg), finite because M(X) ≠ ∞.

1. (Multiplication map.) Apply the sibling smul_testform (Submission.fiw_tb_ext_smul_testForm) with V := ℝ^P (univ), W := U and χ (C^∞, tsupport χ ⊆ U). It gives a linear map L : D^q(ℝ^P) → D^q(U) with (Lω)(x) = χ(x)·ω(x) for all ω and x.
2. (The functional.) Let Y₀ := X ∘ L, i.e. Y₀(ω) = X(Lω). It is linear as a composition of linear maps (X.toCurrent.comp L).
3. (Sequential continuity.) Let (ω_j) be a sequence in D^q(ℝ^P) with TestFormOnConverges ω 0. We show Y₀(ω_j) → 0.
   (a) By the reused sibling converges_small (Submission.fiw_ims_sc_converges_zero_small) with U := ℝ^P: for every δ > 0 there is j₀ such that |ω_j(x)| ≤ δ for all j ≥ j₀ and all x ∈ ℝ^P (eventually_atTop).
   (b) For such j and every x, the sibling norm_smul and |χ(x)| ≤ 1 give |(Lω_j)(x)| = |χ(x)·ω_j(x)| = |χ(x)|·|ω_j(x)| ≤ 1·δ = δ.
   (c) Let ε > 0 and take δ := ε/(μ_X + 1) > 0 in (a). Let j ≥ j₀. Apply the reused sibling eval_bound (Submission.br_la_abs_apply_le_mul_mass) to X ∈ D_q(U), the test form Lω_j ∈ D^q(U), C := δ > 0 (admissible by (b)) and M(X) ≠ ∞. It gives |Y₀(ω_j)| = |X(Lω_j)| ≤ δ·μ_X.
   (d) δ·μ_X = ε·μ_X/(μ_X + 1) < ε, since ε·μ_X < ε·(μ_X + 1) for ε > 0. Hence |Y₀(ω_j) − 0| < ε for all j ≥ j₀. As ε > 0 is arbitrary, Y₀(ω_j) → 0 (Metric.tendsto_atTop).
   So Y := ⟨Y₀, step 3⟩ is an element of GeometricCurrentOn univ q; its continuity field is exactly the statement of step 3.
4. (Characterization.) Let ω ∈ D^q(ℝ^P) and η ∈ D^q(U) with η(x) = χ(x)·ω(x) for every x. Then (Lω)(x) = χ(x)·ω(x) = η(x) for every x. So Lω = η in D^q(U) (Subtype.ext, funext), and Y(ω) = X(Lω) = X(η). ∎

Reference Lean proof (kernel-checked in a scratch build importing GMT.Ch06.Submission, in the comparator's contract scope; sibling dependencies are referenced as Submission.X):
theorem Submission.fiw_tb_ext_cutoff_current : ∀ (P q : ℕ) (U : Set (Eucl P)) (χ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → tsupport χ ⊆ U → (∀ x, |χ x| ≤ 1) → ∀ X : GeometricCurrentOn U q, X.mass ≠ ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) q, ∀ (ω : TestFormOn (univ : Set (Eucl P)) q) (η : TestFormOn U q), (∀ x, (η : DifferentialForm (Eucl P) q) x = χ x • (ω : DifferentialForm (Eucl P) q) x) → Y ω = X η := by
  intro P q U χ hχ hχU hχ1 X hX
  obtain ⟨L, hL⟩ := Submission.fiw_tb_ext_smul_testForm P q (univ : Set (Eucl P)) U χ hχ hχU
  refine ⟨⟨X.toCurrent.comp L, ?_⟩, ?_⟩
  · intro ωs hωs
    obtain ⟨K, -, -, -, hsmall⟩ := Submission.fiw_ims_sc_converges_zero_small P q univ ωs hωs
    rw [Metric.tendsto_atTop]
    intro ε hε
    set μX := X.mass.toReal with hμX
    have hμ0 : 0 ≤ μX := ENNReal.toReal_nonneg
    have hδ : 0 < ε / (μX + 1) := by positivity
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hsmall (ε / (μX + 1)) hδ)
    refine ⟨j₀, fun j hj => ?_⟩
    rw [Real.dist_eq, sub_zero]
    have hbound : ∀ x, covectorEuclideanNorm
        ((L (ωs j) : DifferentialForm (Eucl P) q) x) ≤ ε / (μX + 1) := by
      intro x
      rw [hL, Submission.fiw_tb_ext_covectorNorm_smul]
      calc |χ x| * covectorEuclideanNorm ((ωs j : DifferentialForm (Eucl P) q) x)
          ≤ 1 * (ε / (μX + 1)) :=
            mul_le_mul (hχ1 x) (hj₀ j hj x) (covectorEuclideanNorm_nonneg _) zero_le_one
        _ = ε / (μX + 1) := one_mul _
    have hX' := Submission.br_la_abs_apply_le_mul_mass P q U X (L (ωs j)) (ε / (μX + 1)) hδ hbound hX
    change |X (L (ωs j))| < ε
    calc |X (L (ωs j))| ≤ ε / (μX + 1) * μX := hX'
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  · intro ω η hη
    change X (L ω) = X η
    congr 1
    apply Subtype.ext
    funext x
    rw [hL, hη]

## Key steps

1. L := multiplication by χ, a linear map D^q(ℝ^P) → D^q(U) (sibling smul_testform); Y₀ := X ∘ L.
2. For ω_j → 0: converges_small gives sup_x |ω_j(x)| ≤ δ eventually, and norm_smul with |χ| ≤ 1 gives sup_x |(Lω_j)(x)| ≤ δ.
3. eval_bound: |X(Lω_j)| ≤ δ·M(X); with δ = ε/(M(X) + 1) this is < ε, so Y₀(ω_j) → 0.
4. Y := ⟨X ∘ L, continuity⟩. Lω = η whenever η = χω pointwise, so Y(ω) = X(η).

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
