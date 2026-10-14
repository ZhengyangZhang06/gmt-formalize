# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.im_mass_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 8 of the parent-supplied proof of the selected node dimred_mbl_dtsd_shell_decomposition (the mass measure μ_T := R.measure and the integrality of the shells W_j); Simon, Introduction to GMT, Ch. 6, §5, proof of the deformation theorem 5.1, displays (8)–(10) (book/chapter-06.txt lines 1725–1740). Siblings used: null_off_support (dimred_mbl_dtsd_sh_measure_compl_support_eq_zero) and IR = imrep_restriction (lcmp_imRep_measure_restrict: for every IMRep R in U, (a) R.measure ≪ Hⁿ⌞R.carrier, (b) R.orient is R.measure-a.e. strongly measurable, (c) for every Borel E and every IMRep R′ in U with R′.carrier = R.carrier ∩ E, R′.mult = R.mult and R′.orient = R.orient: R′.measure = R.measure⌞E and R′.action ω = ∫_E R.orient(x)(ω(x)) dR.measure(x) for every form ω).
1. Since T is integer multiplicity, choose an IMRep R in ℝ^P (U = univ) representing T: T(ω) = R.action ω for every ω ∈ 𝒟ⁿ(ℝ^P). Put μ := R.measure and ξ := R.orient.
2. ((5) and (1).) ℝ^P is open, so (MR) with U := ℝ^P gives M_W(T) = μ(W) for every open W, which is (5). For W := ℝ^P this gives μ(ℝ^P) = M_{ℝ^P}(T) = M(T) < ∞ (T.mass is by definition T.massOn univ), so μ is a finite measure (IsFiniteMeasure.mk), which is (1).
3. ((2) and (3).) By IR (b), ξ = R.orient is μ-a.e. strongly measurable, which is (2). By (IMC)(d), for Hⁿ⌞R.carrier-a.e. x we have |ξ(x)(α)| ≤ |α| for every n-covector α. By IR (a), μ ≪ Hⁿ⌞R.carrier, so every property holding Hⁿ⌞R.carrier-a.e. holds μ-a.e. (Measure.AbsolutelyContinuous.ae_le); this is (3).
4. ((4).) Apply IR (c) with the Borel set E := ℝ^P and R′ := R; its hypotheses R.carrier = R.carrier ∩ ℝ^P (Set.inter_univ), R.mult = R.mult and R.orient = R.orient hold. It gives R.action ω = ∫_{ℝ^P} ξ(x)(ω(x)) dμ(x) = ∫ ξ(x)(ω(x)) dμ(x) (setIntegral_univ) for every form ω. Since R represents T, T(ω) = R.action ω = ∫ ξ(x)(ω(x)) dμ(x) for every ω ∈ 𝒟ⁿ(ℝ^P), which is (4).
5. ((6).) By step 2, M_W(T) = μ(W) for every open W, so the sibling null_off_support, applied with (VO), X := T and μ, gives μ(ℝ^P \ spt T) = 0, which is (6).
6. ((7).) Let E be Borel and X ∈ 𝒟_n(ℝ^P) with X(ω) = ∫_E ξ(x)(ω(x)) dμ(x) for all ω ∈ 𝒟ⁿ(ℝ^P). By (IMC)(b) with U := ℝ^P (open), R and E there are A ∈ 𝒟_n(ℝ^P) and an IMRep R′ with R′.carrier = R.carrier ∩ E, R′.mult = R.mult and R′.orient = R.orient (that R′ represents A is not needed). By IR (c) applied to E and R′, R′.action ω = ∫_E R.orient(x)(ω(x)) dR.measure(x) = ∫_E ξ(x)(ω(x)) dμ(x) = X(ω) for every ω ∈ 𝒟ⁿ(ℝ^P). Hence R′ represents X, and X is integer multiplicity.
7. Steps 2–6 show that μ and ξ have properties (1)–(7). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration `theorem Submission.dimred_mbl_dtsd_sh_im_mass_measure : T := by` followed by the tactic block below, where T is this child's frozen Lean type (field lean_statement) verbatim, was compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308. It was placed after `import GMT.Ch07.Submission` in the child comparator scope (inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`) and uses the sibling declarations Submission.dimred_mbl_dtsd_sh_measure_compl_support_eq_zero (null_off_support) and Submission.lcmp_imRep_measure_restrict (imrep_restriction) (each available as a declaration of its frozen type). The antecedents of the statement are hypotheses of the theorem, so no other DAG declaration is used. The comparator solution `exact Submission.dimred_mbl_dtsd_sh_im_mass_measure` closes the frozen challenge type, and `#print axioms` reports only propext, Classical.choice and Quot.sound beyond those sibling declarations.

```lean
  intro hVO hMR hIMC P n T hT hTm
  obtain ⟨R, hR⟩ := hT
  obtain ⟨hac, hξm, hres⟩ := Submission.lcmp_imRep_measure_restrict P n univ R
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W :=
    hMR P n univ T R isOpen_univ hR
  have hfin : IsFiniteMeasure R.measure := ⟨by rw [← hmass univ isOpen_univ]; exact hTm⟩
  refine ⟨R.measure, R.orient, hfin, hξm, hac.ae_le (hIMC.2.2.2 P n univ R), ?_, hmass,
    Submission.dimred_mbl_dtsd_sh_measure_compl_support_eq_zero hVO P n T R.measure hmass, ?_⟩
  · intro ω
    rw [hR ω, (hres univ R MeasurableSet.univ (Set.inter_univ _).symm rfl rfl).2, setIntegral_univ]
  · intro E X hE hX
    obtain ⟨A, R', -, hcar, hmult, horient⟩ := hIMC.2.1 P n univ R E isOpen_univ hE
    refine ⟨R', fun ω => ?_⟩
    rw [hX ω, (hres E R' hE hcar hmult horient).2]
```

## Key steps

1. Choose an IMRep R of T; μ := R.measure, ξ := R.orient.
2. (MR) gives M_W(T) = μ(W) for open W, hence μ(ℝ^P) = M(T) < ∞ and μ is finite.
3. IR (a), (b) and (IMC)(d) give a.e. strong measurability of ξ and the μ-a.e. bound |ξ(x)(α)| ≤ |α|.
4. IR (c) with E = ℝ^P, R′ = R gives T(ω) = ∫ ξ(ω) dμ.
5. null_off_support with (VO) gives μ(ℝ^P \ spt T) = 0.
6. (IMC)(b) gives an IMRep R′ with carrier R.carrier ∩ E; IR (c) shows R′.action = ∫_E ξ(ω) dμ = X(ω), so X is IM.

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
