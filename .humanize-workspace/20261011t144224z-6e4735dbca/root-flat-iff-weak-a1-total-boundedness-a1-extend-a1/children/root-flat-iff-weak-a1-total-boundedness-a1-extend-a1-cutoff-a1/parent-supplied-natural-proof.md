# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (Cutoff) of the parent proof of fiw_tb_extend_to_univ, written out for ℝ^P = EuclideanSpace ℝ (Fin P). This is a finite-dimensional real normed space, hence locally compact and Hausdorff, so its compact subsets are closed.

1. (Two compact neighbourhoods.) K is compact, U is open and K ⊆ U. By local compactness there is a compact set L with K ⊆ interior L and L ⊆ U (Mathlib exists_compact_between). Apply the same fact to K and the open set interior L (isOpen_interior; K ⊆ interior L). This gives a compact set L₁ with K ⊆ interior L₁ and L₁ ⊆ interior L.
2. (Smooth Urysohn function.) L₁ is compact, hence closed; interior L is open; and L₁ ⊆ interior L. The smooth Urysohn lemma for finite-dimensional real normed spaces (Mathlib exists_contDiff_support_eq_eq_one_iff with smoothness n := (⊤ : ℕ∞), s := interior L, t := L₁) gives f : ℝ^P → ℝ with:
   - ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f;
   - range f ⊆ [0, 1];
   - support f = interior L;
   - for every x, x ∈ L₁ ⟺ f(x) = 1.
   (Alternatively, use exists_contMDiffMap_one_nhds_of_subset_interior with the model 𝓘(ℝ, ℝ^P), s := K, t := L, then contMDiff_iff_contDiff. The argument below only needs the listed properties.)
3. Put χ := f and N := interior L₁.
   (a) χ is C^∞ by step 2.
   (b) For every x, χ(x) ∈ range f ⊆ [0, 1], i.e. 0 ≤ χ(x) ≤ 1.
   (c) support χ = interior L ⊆ L, and L is closed. So tsupport χ = closure(support χ) ⊆ L (closure_minimal), hence tsupport χ ⊆ L ⊆ U.
   (d) tsupport χ is closed (isClosed_tsupport) and contained in the compact set L, so it is compact (IsCompact.of_isClosed_subset). That is, HasCompactSupport χ.
   (e) N = interior L₁ is open (isOpen_interior), and K ⊆ N by step 1.
   (f) If x ∈ N then x ∈ L₁ (interior_subset), so χ(x) = 1 by step 2.
4. Properties (a)–(f) are exactly the assertions of the lemma. ∎

Reference Lean proof (kernel-checked in a scratch build importing GMT.Ch06.Submission, in the comparator's contract scope; sibling dependencies are referenced as Submission.X):
theorem Submission.fiw_tb_ext_cutoff : ∀ (P : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∃ (χ : Eucl P → ℝ) (N : Set (Eucl P)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, χ x = 1 := by
  intro P U K hU hK hKU
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨L₁, hL₁, hKL₁, hL₁L⟩ := exists_compact_between hK isOpen_interior hKL
  obtain ⟨f, hf, hfr, hfs, hf1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) isOpen_interior hL₁.isClosed hL₁L
  have htsupp : tsupport f ⊆ L :=
    closure_minimal (hfs.symm ▸ interior_subset) hL.isClosed
  refine ⟨f, interior L₁, hf, fun x => hfr (mem_range_self x), ?_, htsupp.trans hLU,
    isOpen_interior, hKL₁, fun x hx => (hf1 x).mp (interior_subset hx)⟩
  exact hL.of_isClosed_subset (isClosed_tsupport _) htsupp

## Key steps

1. exists_compact_between twice: compact L, L₁ with K ⊆ interior L₁ ⊆ L₁ ⊆ interior L ⊆ L ⊆ U.
2. Smooth Urysohn (exists_contDiff_support_eq_eq_one_iff): f is C^∞ with values in [0, 1], support f = interior L, and f = 1 exactly on L₁.
3. tsupport f ⊆ L because L is closed; hence f has compact support contained in U.
4. N := interior L₁ is open, contains K, and f = 1 on N.

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
