# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.eq_near-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 (vanishing fact (V)) of the parent proof, in the form used in steps 5, 8 and (B5). There η = χ•ω with χ = 1 on N, so η and ω agree on N. The hypothesis "Z vanishes on test forms supported off K" replaces the parent's appeal to spt Z ⊆ K and vanish_off_support; the parent derives this hypothesis from spt Z ⊆ K.

1. Put ζ := η − ω ∈ D^q(V). D^q(V) is a real vector space with pointwise operations, so ζ(x) = η(x) − ω(x). For x ∈ N, ζ(x) = 0 by hypothesis. Hence support ζ ⊆ ℝ^P ∖ N.
2. N is open, so ℝ^P ∖ N is closed. Therefore tsupport ζ = closure(support ζ) ⊆ ℝ^P ∖ N (closure_minimal).
3. K ⊆ N, so ℝ^P ∖ N is disjoint from K. By step 2, tsupport ζ is disjoint from K.
4. By the hypothesis on Z, Z(ζ) = 0. Z is linear (Z.toCurrent is a linear map; map_sub), so Z(ζ) = Z(η) − Z(ω). Hence Z(η) = Z(ω). ∎

Reference Lean proof (kernel-checked in a scratch build importing GMT.Ch06.Submission, in the comparator's contract scope; sibling dependencies are referenced as Submission.X):
theorem Submission.fiw_tb_ext_apply_eq_of_eqOn : ∀ (P q : ℕ) (V K N : Set (Eucl P)) (Z : GeometricCurrentOn V q), IsOpen N → K ⊆ N → (∀ ω : TestFormOn V q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → ∀ ω η : TestFormOn V q, (∀ x ∈ N, (η : DifferentialForm (Eucl P) q) x = (ω : DifferentialForm (Eucl P) q) x) → Z η = Z ω := by
  intro P q V K N Z hN hKN hZ ω η hηω
  have hsupp : tsupport ((η - ω : TestFormOn V q) : DifferentialForm (Eucl P) q) ⊆ Nᶜ := by
    apply closure_minimal _ hN.isClosed_compl
    intro x hx hxN
    apply hx
    change (η : DifferentialForm (Eucl P) q) x - (ω : DifferentialForm (Eucl P) q) x = 0
    rw [hηω x hxN, sub_self]
  have h0 : Z (η - ω) = 0 :=
    hZ _ (Disjoint.mono_left hsupp (disjoint_compl_left.mono_right hKN))
  have h1 : Z (η - ω) = Z η - Z ω := Z.toCurrent.map_sub η ω
  rw [h1] at h0
  exact sub_eq_zero.mp h0

## Key steps

1. ζ := η − ω vanishes on the open set N, so tsupport ζ ⊆ ℝ^P ∖ N.
2. ℝ^P ∖ N is disjoint from K ⊆ N, so Z(ζ) = 0 by hypothesis.
3. Linearity: Z(η) − Z(ω) = Z(ζ) = 0.

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
