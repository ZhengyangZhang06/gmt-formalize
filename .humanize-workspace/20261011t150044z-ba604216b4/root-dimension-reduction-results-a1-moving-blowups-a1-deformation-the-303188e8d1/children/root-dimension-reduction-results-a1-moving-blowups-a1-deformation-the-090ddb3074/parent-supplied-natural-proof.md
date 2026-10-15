# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.boundary_mass_calculus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the boundary-mass bookkeeping of step 12 of the parent-supplied proof of the selected node dimred_mbl_dtsd_shell_decomposition ((X − Y).boundary = ∂X − ∂Y, ∂∂ = 0, M(0) = 0 and MS). Sibling used: MS = mass_sub (cmc_fc_cs_massOn_sub_le: M_G(A − B) ≤ M_G(A) + M_G(B) for all U, G and A, B ∈ 𝒟_n(U)).
1. (M_G(0) = 0 in every degree.) M_G(0) is the supremum of ENNReal.ofReal 0(ω) = ENNReal.ofReal 0 = 0 over the admissible ω (GeometricCurrentOn.zero_apply), so M_G(0) ≤ 0 (sSup_le), i.e. M_G(0) = 0.
2. (m = 0.) boundaryMassOn of any current of degree 0 is 0 by definition. So (a) reads 0 ≤ 0 + 0, and (b), for the 0-current ∂X, reads 0 = 0.
3. (m = k + 1, part (a).) For Z ∈ 𝒟_{k+1}(U), boundaryMassOn Z G = M_G(∂Z) by definition. For η ∈ 𝒟^k(U), ∂(X − Y)(η) = (X − Y)(dη) = X(dη) − Y(dη) = ∂X(η) − ∂Y(η) = (∂X − ∂Y)(η) (all definitional), so ∂(X − Y) = ∂X − ∂Y (GeometricCurrentOn.ext). By MS (with k, U, G, ∂X, ∂Y), M_G(∂(X − Y)) = M_G(∂X − ∂Y) ≤ M_G(∂X) + M_G(∂Y), which is (a).
4. (m = k + 1, part (b).) For X ∈ 𝒟_{k+2}(U), ∂X ∈ 𝒟_{k+1}(U) and boundaryMassOn (∂X) G = M_G(∂∂X) = M_G(0) = 0 by GeometricCurrentOn.boundary_boundary and step 1. ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration `theorem Submission.dimred_mbl_dtsd_sh_boundaryMassOn_calculus : T := by` followed by the tactic block below, where T is this child's frozen Lean type (field lean_statement) verbatim, was compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308. It was placed after `import GMT.Ch07.Submission` in the child comparator scope (inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`) and uses the sibling declaration Submission.cmc_fc_cs_massOn_sub_le (mass_sub) (available as a declaration of its frozen type). No other DAG declaration is used. The comparator solution `exact Submission.dimred_mbl_dtsd_sh_boundaryMassOn_calculus` closes the frozen challenge type, and `#print axioms` reports only propext, Classical.choice and Quot.sound beyond those sibling declarations.

```lean
  intro P m U G
  have hzero : ∀ {k : ℕ} (G : Set (Euclid P)), (0 : GeometricCurrentOn U k).massOn G = 0 := by
    intro k G
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, -, rfl⟩
    simp
  cases m with
  | zero => exact ⟨fun X Y => by simp [boundaryMassOn], fun X => rfl⟩
  | succ k =>
    refine ⟨fun X Y => ?_, fun X => ?_⟩
    · show (X - Y).boundary.massOn G ≤ X.boundary.massOn G + Y.boundary.massOn G
      have h : (X - Y).boundary = X.boundary - Y.boundary := by ext ω; rfl
      rw [h]
      exact Submission.cmc_fc_cs_massOn_sub_le P k U G _ _
    · show X.boundary.boundary.massOn G = 0
      rw [GeometricCurrentOn.boundary_boundary]
      exact hzero G
```

## Key steps

1. M_G(0) = 0 (sSup of ofReal 0).
2. Degree 0: boundaryMassOn is identically 0.
3. Degree k + 1: ∂(X − Y) = ∂X − ∂Y (ext), then MS.
4. ∂∂X = 0 (boundary_boundary), so boundaryMassOn (∂X) G = M_G(0) = 0.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db, mathlib_commit 25730c7c); git rev-parse HEAD (b4d606db); git -C .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cmp .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n "def boundaryMassOn|structure IMRep|def IMRep.Represents|def IsIntegerMultiplicity|def IMRep.measure|def IMRep.action|instance : Sub \(GeometricCurrentOn|def CompactlyContained|abbrev MultiVector" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (lines 48, 61, 79, 83, 88, 92, 96, 120, 127)`
- `rg -n "isOpen_zeroRegion|boundary_boundary|massOn_mono|le_massOn|zero_apply|boundary_apply" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (GeometricCurrentOn.zero_apply, boundary_apply, boundary_boundary in Currents.lean 317/333/365; massOn_mono, le_massOn in Mass.lean 81/90; isOpen_zeroRegion in CurrentLocalEquality.lean 119)`
- `rg -n "theorem integral_add_compl|theorem setIntegral_sdiff|theorem summable_toReal|theorem measure_iUnion|theorem strictAnti_nat_of_succ_lt|theorem tendsto_pow_atTop_nhds_zero_of_lt_one|theorem integral_eq_zero_of_ae|theorem integral_zero_measure|theorem tendsto_add_atTop_iff_nat|theorem measure_eq_zero_iff_ae_notMem" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib (all found)`
- `rg -n -i -l "shell|dyadic|good_radius|goodRadius" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT -g "*.lean" (no match, exit 1); rg -n -i "theorem .*slice|def .*slice" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT -g "*.lean" (only the specification definitions IsSlice in Ch06 Contract/Submission line 129, not imported by Ch07, and SlicesAreRectifiable in Ch03 line 262)`
- `rg -n "dimred_mbl_dtsd_sh_" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/.. (no match, exit 1); python3 -I scan of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json (2138 nodes): no lean_name equals a fresh name or starts with dimred_mbl_dtsd_sh_; the reused names are accepted nodes with byte-identical frozen types`
- `python3 -I scan of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: the selected frozen type is byte-identical to the twin node's; the twin's ten child types (decomposition-v1.json of the twin node directory) are reused verbatim; the six resolved dependencies of the selected node have frozen types byte-identical to the twin's six; no accepted node other than the twin's unaccepted children carries any of the seven new types`
- `sed of /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _render_parent_supplied_natural) and inherited.py (cited, cited_inherited); python3 -I check with that cited() that no new child proof, key step or this ledger names a not-yet-accepted dependency of the selected node or of its ancestors`
- `lake-env lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/EndToEnd.lean (the twin's verified file renamed to this branch's names, accepted ML proof of commit 1041782e inlined; #print axioms: children only propext, Classical.choice, Quot.sound; selected theorem additionally only the two unaccepted resolved dependencies); python3 -I GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/scripts/compare_types.py (all declared types byte-identical to the frozen ones)`
- `lake-env lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/AssemblyAx.lean (selected type from the ten child and six dependency types as axioms); lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/isolated/Iso_*.lean (each new child with only its declared siblings as axioms, then the comparator solution exact Submission.X)`
- `python3 -I GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/scripts/build_challenges.py with the verifier's child_modules(contract mode) and lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/chal/Challenge_*.lean (11 files, 0 errors, one sorry warning each); python3 -I GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/scripts/validate.py (runtime and verifier validate_lean_statement: all accepted unchanged)`
- `git show ae810e9b/ea5c1199/7a706164/1041782e:GMT/Ch07/Submission.lean + #print axioms, compiled with lean (errors 0; propext, Classical.choice, Quot.sound only)`
- `sed -n 1700,1800p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt (Simon 6.5.1 displays (8)–(10) at lines 1725–1740)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Monotone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-303188e8d1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-691b18cd91/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-691b18cd91/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-691b18cd91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9b75b9802b/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_shell_decomposition_split/EndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/EndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/types.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`

Pins match (project b4d606db, Mathlib 25730c7c), and Submission.lean is byte-identical to the frozen contract. The snapshot project has no shell, dyadic or good-radius declaration; "slice" occurs there only in the specification definitions IsSlice (Ch06, not imported by Ch07) and SlicesAreRectifiable (Ch03), so no snapshot lemma can replace a child. The fresh prefix dimred_mbl_dtsd_sh_ occurs nowhere in the project, Mathlib, SimonGMT or the DAG. Every Mathlib and SimonGMT lemma that the child proofs cite exists at the pinned revisions. The twin node's audited split applies verbatim, because its frozen type and its six resolved-dependency types are byte-identical to the selected node's. Its seven new child types are reused unchanged under fresh names, since its own child names are reserved and unaccepted. Its three reused declarations are accepted with identical types and recompile from their accepted commits with standard axioms. In this session:
- the children's proofs and the assembly compile;
- each new child compiles alone with only its declared siblings;
- the comparator challenge modules elaborate, and both statement validators accept every type unchanged;
- the assembly proves the exact selected type from the child and dependency types;
- no new child proof, key step or this ledger cites a not-yet-accepted inherited prerequisite.
