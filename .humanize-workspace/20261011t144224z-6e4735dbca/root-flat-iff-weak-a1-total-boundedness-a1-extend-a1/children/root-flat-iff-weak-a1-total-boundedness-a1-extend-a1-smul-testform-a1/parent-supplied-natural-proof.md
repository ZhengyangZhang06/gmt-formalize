# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.smul_testform-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 (Products with χ) of the parent proof, for arbitrary source and target domains.

Notation. For ω ∈ D^q(V) = TestFormOn V q we also write ω for the underlying form (ω : DifferentialForm (Eucl P) q). By definition of TestFormOn (testFormOnSubmodule), a form φ : ℝ^P → Covector (Eucl P) q belongs to TestFormOn W q iff:
- φ is C^∞ (IsSmoothForm φ, i.e. ContDiff ℝ ∞ φ);
- HasCompactSupport φ;
- tsupport φ ⊆ W.
The vector-space operations of TestFormOn W q are pointwise. Two elements are equal iff their underlying forms are equal (Subtype.ext).

1. Fix ω ∈ D^q(V) and put φ_ω(x) := χ(x)·ω(x).
   (a) Smoothness. χ : ℝ^P → ℝ is C^∞, and ω : ℝ^P → Covector (Eucl P) q is C^∞ since ω ∈ D^q(V). So the pointwise scalar product φ_ω is C^∞ (ContDiff.smul).
   (b) Compact support.
       - tsupport φ_ω ⊆ tsupport ω (tsupport_smul_subset_right), and tsupport ω is compact (HasCompactSupport ω).
       - tsupport φ_ω is closed (isClosed_tsupport), so it is compact (IsCompact.of_isClosed_subset), i.e. HasCompactSupport φ_ω.
       - No compactness of tsupport χ is needed.
   (c) Support in W. tsupport φ_ω ⊆ tsupport χ ⊆ W, by tsupport_smul_subset_left and the hypothesis.
   Hence φ_ω ∈ TestFormOn W q.
2. Define L(ω) := ⟨φ_ω, step 1⟩ ∈ D^q(W). By construction (Lω)(x) = χ(x)·ω(x) for all x.
3. L is ℝ-linear. Both identities are checked on underlying forms at every point x (Subtype.ext, funext):
   (a) L(ω₁ + ω₂)(x) = χ(x)·(ω₁(x) + ω₂(x)) = χ(x)·ω₁(x) + χ(x)·ω₂(x) = (Lω₁ + Lω₂)(x) (smul_add);
   (b) for c ∈ ℝ, L(cω)(x) = χ(x)·(c·ω(x)) = c·(χ(x)·ω(x)) = (c·Lω)(x) (smul_comm).
   So L, with map_add' from (a) and map_smul' from (b), is a linear map TestFormOn V q →ₗ[ℝ] TestFormOn W q.
4. L satisfies the asserted pointwise formula (step 2). ∎

Reference Lean proof (kernel-checked in a scratch build importing GMT.Ch06.Submission, in the comparator's contract scope; sibling dependencies are referenced as Submission.X):
theorem Submission.fiw_tb_ext_smul_testForm : ∀ (P q : ℕ) (V W : Set (Eucl P)) (χ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → tsupport χ ⊆ W → ∃ L : TestFormOn V q →ₗ[ℝ] TestFormOn W q, ∀ (ω : TestFormOn V q) (x : Eucl P), (L ω : DifferentialForm (Eucl P) q) x = χ x • (ω : DifferentialForm (Eucl P) q) x := by
  intro P q V W χ hχ hχW
  have hmem : ∀ ω : TestFormOn V q,
      (fun x => χ x • (ω : DifferentialForm (Eucl P) q) x) ∈ TestFormOn W q := by
    intro ω
    obtain ⟨⟨hs, hc⟩, -⟩ := ω.property
    refine ⟨⟨hχ.smul hs, ?_⟩, (tsupport_smul_subset_left _ _).trans hχW⟩
    exact hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _)
  refine ⟨{ toFun := fun ω => ⟨_, hmem ω⟩, map_add' := ?_, map_smul' := ?_ }, fun ω x => rfl⟩
  · intro a b
    apply Subtype.ext
    funext x
    change χ x • ((a : DifferentialForm (Eucl P) q) x + (b : DifferentialForm (Eucl P) q) x) = _
    rw [smul_add]
    rfl
  · intro c a
    apply Subtype.ext
    funext x
    change χ x • (c • (a : DifferentialForm (Eucl P) q) x) =
      c • (χ x • (a : DifferentialForm (Eucl P) q) x)
    rw [smul_comm]

## Key steps

1. For ω ∈ D^q(V), χ·ω is C^∞ (ContDiff.smul), has compact support (tsupport ⊆ tsupport ω), and tsupport ⊆ tsupport χ ⊆ W, so χ·ω ∈ D^q(W).
2. L(ω) := χ·ω satisfies the pointwise formula by construction.
3. Additivity and homogeneity hold pointwise (smul_add, smul_comm), so L is linear.

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
