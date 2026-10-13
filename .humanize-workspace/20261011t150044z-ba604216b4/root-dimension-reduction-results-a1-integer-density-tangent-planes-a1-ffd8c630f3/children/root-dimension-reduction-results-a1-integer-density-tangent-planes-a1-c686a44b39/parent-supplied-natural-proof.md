# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.sheet_first_variation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.sheet_first_variation-a1.mult_const-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1 and 3. Step 3 identifies θ through the a.e. equality Θⁿ(μ_T, x) = θ(x). That equality is Simon Ch. 3, Remark 1.8(2) (chapter-03.txt, lines 298–313), with μ_T = μ_V by Ch. 6, Remark 3.2(3), and the accepted lemma `Submission.rsd_ae_hasMassDensity_mult` encodes it. Conventions: Hⁿ := μHE[n]; Hⁿ⌞A := μHE[n].restrict A; S := R.carrier; θ := R.mult (read in ℝ≥0∞ where needed); B := ball p ρ; μ := R.measure = (Hⁿ⌞S).withDensity θ. No assumption on ρ is used: if ρ ≤ 0 then B = ∅, and the argument below covers this case.
1. (spt T carries Hⁿ⌞S.) By the accepted lemma `Submission.imrep_carrier_sdiff_support_null` (U open, R represents T), Hⁿ(S ∖ spt T) = 0. S is measurable (field measurableSet_carrier), so Measure.restrict_apply' gives (Hⁿ⌞S)((spt T)ᶜ) = Hⁿ((spt T)ᶜ ∩ S) = Hⁿ(S ∖ spt T) = 0. Hence Hⁿ⌞S-a.e. x lies in spt T.
2. (spt T carries μ.) μ is a withDensity measure over Hⁿ⌞S, so μ ≪ Hⁿ⌞S (withDensity_absolutelyContinuous). By step 1, μ-a.e. x lies in spt T.
3. (Conclusion (a).) By the accepted lemma `Submission.rsd_ae_hasMassDensity_mult` (U open, R represents T), HasMassDensity T x θ(x) for μ-a.e. x. Take x with this property and with x ∈ spt T (μ-a.e. x has both, by step 2), and suppose x ∈ B. Then x ∈ spt T ∩ B, so HasMassDensity T x k by hypothesis. The accepted uniqueness lemma `Submission.dimred_cs_mi_hasMassDensity_unique` gives (θ(x) : ℝ) = (k : ℝ), hence θ(x) = k, because the cast ℕ → ℝ is injective. Thus ∀ᵐ x ∂μ, x ∈ B → θ(x) = k, which is the first conjunct.
4. (Hⁿ⌞S ≪ μ.) The function x ↦ (θ(x) : ℝ≥0∞) is measurable: it is field measurable_mult composed with the measurable cast ℕ → ℝ≥0∞. It is nonzero Hⁿ⌞S-a.e., because Hⁿ⌞S-a.e. x lies in S (ae_restrict_mem, S measurable) and θ(x) > 0 for x ∈ S (field mult_pos). By withDensity_absolutelyContinuous', Hⁿ⌞S ≪ (Hⁿ⌞S).withDensity θ = μ. Concretely: if A is measurable and μ(A) = ∫_{A∩S} θ dHⁿ = 0, then θ = 0 Hⁿ-a.e. on A ∩ S, so Hⁿ(A ∩ S) = 0 because θ ≥ 1 on S.
5. (Conclusion (b).) By steps 3 and 4, x ∈ B → θ(x) = k holds Hⁿ⌞S-a.e. Since S ∩ B ⊆ S, we have Hⁿ⌞(S ∩ B) ≤ Hⁿ⌞S (Measure.restrict_mono), so the implication also holds Hⁿ⌞(S ∩ B)-a.e. S ∩ B is measurable (S measurable, B open), so Hⁿ⌞(S ∩ B)-a.e. x lies in S ∩ B ⊆ B (ae_restrict_mem). Combining the two, θ(x) = k for Hⁿ⌞(S ∩ B)-a.e. x, which is the second conjunct. ∎

## Key steps

1. Hⁿ(S ∖ spt T) = 0 (imrep_carrier_sdiff_support_null). Hence Hⁿ⌞S-a.e. points lie in spt T, and so do μ-a.e. points, since μ ≪ Hⁿ⌞S.
2. μ-a.e. x has density θ(x) (rsd_ae_hasMassDensity_mult). At such x ∈ spt T ∩ B the density is also k, so θ(x) = k by uniqueness (dimred_cs_mi_hasMassDensity_unique). This is conclusion (a).
3. θ ≥ 1 on S gives Hⁿ⌞S ≪ μ (withDensity_absolutelyContinuous'), so (a) holds Hⁿ⌞S-a.e.
4. Restrict from Hⁿ⌞S to Hⁿ⌞(S ∩ B), under which a.e. point lies in B. This gives conclusion (b).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `python3 -I scans of dag.json (lean_name, lean_statement, status): the 9 cited lemmas imrep_carrier_sdiff_support_null, rsd_ae_hasMassDensity_mult, dimred_cs_mi_hasMassDensity_unique, regcomp_atl_local_density_zero, rsd_massOn_eq_measure, dtc_approxTangent_of_null_diff, approxTangent_le_submanifold_tangentSpace, chart_tangentSpace_eq_range_fderiv, dpf_itt_approxTangentPlane_eq; statements mentioning tangentSpace together with finrank or span; approxTangentPlane; firstVariation; conclusions of the form 'R.mult x = …' together with HasMassDensity; support-minus-carrier null sets; children of cone_constant_density_planar`
- `grep -o 'idtp_ccd_[A-Za-z0-9_]*' dag.json; grep -rl 'idtp_ccd_sfv' in run nodes/, decomposition-reopenings/, operator-dependency-edits/, cluster-state/verification and .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match)`
- `grep -n 'def support|def zeroRegion|def VanishesOn|isOpen_zeroRegion' simongmt Chapter06/CurrentLocalEquality.lean and Chapter06/Currents.lean; grep -n 'def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique|HasApproximateTangentSpaceAt.finrank_eq' simongmt Chapter03/Rectifiable.lean`
- `grep -rn in pinned Mathlib for setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_congr_set, integral_const_mul, integral_congr_ae, ae_eq_set, support_fderiv_subset, withDensity_absolutelyContinuous', ENNReal.mul_div_mul_comm, Submodule.eq_of_le_of_finrank_eq, LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin, setLIntegral_mono', setLIntegral_one, ENNReal.Tendsto.const_mul, le_of_tendsto_of_tendsto, measure_ball_lt_top, measure_ball_pos, ball_subset_ball', Ioo_mem_nhdsGT and ENNReal.ofReal_pow; cmp of the 12 containing files between local-references/123e8435b4a2469b/mathlib and .lake/packages/mathlib (all identical)`
- `grep -n 'theorem Submission.dpf_itt_approxTangentPlane_eq' and the namespace/open lines in .swarm-worktrees/71cd69b7a778a035ba27/gmt-ch07/GMT/Ch07/Submission.lean (declaration convention)`
- `grep -n and sed in book/chapter-01.txt (3.6 Theorem, 3.7 Remarks, lines 700–711), chapter-02.txt (§4, (4.3), lines 845–871), chapter-03.txt (1.4 Definition, 1.5 Remarks lines 86–90, 1.8 Remarks lines 298–313), chapter-04.txt (line 350, Remark 1.8(2)) and chapter-06.txt (3.2 Remarks (3), lines 755–770)`
- `sed of the sibling parent-supplied-natural-proof.md files of regular_of_const_density (…-1948384b6f) and stationary_cone_sheet_planar (…-3876084c61), to check reuse`
- `lake env lean /tmp/sfv_check/Children.lean: the 4 child types elaborate after import GMT.Ch07.Submission`
- `lake env lean on /tmp/sfv_check/Assembly.lean, ChildDC.lean, ChildA.lean and ChildB.lean: each child and the parent proved from stub hypotheses, with axioms propext, Classical.choice, Quot.sound`
- `python3 -I /tmp/sfv_scripts/gen_defs.py dag.json children.json defs.inc, then lake env lean /tmp/sfv_check/Combined.lean: #print axioms chk_end_to_end and chk_parent = [propext, Classical.choice, Quot.sound]`
- `independent reviewer agent re-ran Combined.lean and /tmp/sfv_review/Sim.lean (Submission.* axiom stubs) and ran a byte-identity check (/tmp/sfv_review/check_bytes.py)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ffd8c630f3/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ffd8c630f3/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ffd8c630f3/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-1948384b6f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3876084c61/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/71cd69b7a778a035ba27/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/sfv_check/Children.lean`
- `/tmp/sfv_check/Assembly.lean`
- `/tmp/sfv_check/ChildDC.lean`
- `/tmp/sfv_check/ChildA.lean`
- `/tmp/sfv_check/ChildB.lean`
- `/tmp/sfv_check/Combined.lean`
- `/tmp/sfv_check/children.json`
- `/tmp/sfv_check/draft.json`
- `/tmp/sfv_scripts/gen_defs.py`
- `/tmp/sfv_review/Sim.lean`

The pins match the manifest. Project HEAD is b4d606d, Mathlib is 25730c7c and SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The 12 Mathlib files consulted are identical between the snapshot and .lake/packages/mathlib.

All 9 lemmas cited by the children and the parent assembly are DAG nodes with status `accepted`, and each child applies them with hypotheses that match their dag.json types:
- imrep_carrier_sdiff_support_null
- rsd_ae_hasMassDensity_mult
- dimred_cs_mi_hasMassDensity_unique
- regcomp_atl_local_density_zero
- rsd_massOn_eq_measure
- dtc_approxTangent_of_null_diff
- approxTangent_le_submanifold_tangentSpace
- chart_tangentSpace_eq_range_fderiv
- dpf_itt_approxTangentPlane_eq

No accepted lemma already states any child:
- Nothing gives finrank or carrier equality of span(tangentSpace M x).
- Nothing gives Hⁿ-a.e. constancy of mult from constant density on the support.
- Nothing gives Hⁿ((spt T ∩ B) ∖ carrier) = 0 under constant positive density; dorag_support_sdiff_carrier_null needs a bounded mean curvature hypothesis instead.
- Nothing gives a.e. equality of approxTangentPlane with the tangent span of a containing C¹ submanifold; dsmc_approxTangentPlane_subset_tangentSpace and approxTangent_le_submanifold_tangentSpace give only containment.

The siblings regular_of_const_density (its step 4) and stationary_cone_sheet_planar (its step 1) re-derive mult_const(a) and tangent_space_dim, so the children are reusable.

The SimonGMT facts used hold as cited:
- HasApproximateTangentSpaceAt includes finrank = n as its first component.
- HasApproximateTangentSpaceAt.unique and HasApproximateTangentSpaceAt.finrank_eq exist.
- spt T = U ∖ zeroRegion with zeroRegion open.
All cited Mathlib names exist at the pinned revision.

The proposed names idtp_ccd_sfv_* are unreserved: they appear nowhere in dag.json, the run directories, cluster-state verification or any worktree Submission.lean.

Lean checks: the 4 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract's opens. Combined.lean takes the verbatim accepted-lemma, child and frozen-parent types and proves each child and then the parent; its axioms are propext, Classical.choice and Quot.sound. The independent reviewer re-ran it, confirmed byte identity, and found no defects.

Book sources:
- Ch. 1, Theorem 3.6 and Remark 3.7(2)
- Ch. 2, (4.3)
- Ch. 3, Remarks 1.5(2) and 1.8(2)
- Ch. 6, Remark 3.2(3)
