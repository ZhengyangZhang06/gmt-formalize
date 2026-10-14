# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.filling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the selected proof's step 3 (V3: a compactly supported IM filling Y of ∂T, by the isoperimetric theorem when n = d + 1 ≥ 2 and by signed segments from a point when n = 1, the total multiplicity being zero by (VO)); Simon Ch. 6, 6.1 (isoperimetric theorem) and 8.2 (“the general case of the theorem follows from the special case when ∂T = 0”). Uses the siblings support_vanish (Lean name rsd_cmr_support_subset_of_vanish), current_algebra (cbr_cc_current_algebra), segment_current (dmcbr_cc_segment_current) and zero_current_sum (dmcbr_cc_zero_current_finite_sum). The selected proof takes the base point x₀ of the segments outside {x_1, …, x_N}; since segment_current also allows coincident endpoints, the base point 0 works in every case (including P = 0 and N = 0). (The same Lean type is frozen in another branch under the name cbr_cc_compact_im_filling.)
1. spt ∂T ⊆ spt T, and spt ∂T is compact. If η ∈ 𝒟^d(ℝ^P) has tsupport disjoint from spt T, then tsupport(dη) ⊆ tsupport η (tsupport_exteriorDerivative_subset), so ∂T(η) = T(dη) = 0 by (VO). support_vanish with U := ℝ^P and K := spt T (compact) gives spt ∂T ⊆ spt T and spt ∂T compact.
Case d = m + 1 ≥ 1.
2. Z := ∂T ∈ 𝒟_{m+1}(ℝ^P) is integer multiplicity, has compact support (step 1), ∂Z = ∂∂T = 0 (GeometricCurrentOn.boundary_boundary) and M(Z) < ∞. (ISO) with P and m gives c ≥ 1 and an integer multiplicity Y ∈ 𝒟_{m+2}(ℝ^P) = 𝒟_{d+1}(ℝ^P) with ∂Y = Z = ∂T, M(Y) ≤ ofReal(c(2cM(Z))^{1/(m+1)}M(Z)) < ∞, and spt Y ⊆ thickening(r, spt Z) with r := 3√P(2cM(Z))^{1/(m+1)}.
3. spt Y is compact: spt Z is compact, hence bounded, so thickening(r, spt Z) is bounded and its closure C is compact (ℝ^P is proper). If tsupport ω is disjoint from C, it is disjoint from spt Y, so Y(ω) = 0 by (VO); support_vanish with K := C gives that spt Y is compact.
Case d = 0.
4. By step 1 and zero_current_sum (with (MR) and (VO)) applied to the integer multiplicity, compactly supported ∂T ∈ 𝒟_0(ℝ^P), there are a finite F ⊆ spt ∂T and integers m(x) with ∂T(g) = Σ_{x∈F} m(x)g(x)⟨⟩ for every test 0-form g.
5. Total multiplicity zero: Σ_{x∈F} m(x) = 0. Choose ρ > 0 with spt T ⊆ B_ρ(0) (spt T is compact, hence bounded). Let ψ be a smooth bump function with compact support and ψ = 1 on B̄_ρ(0) (ContDiffBump centred at 0 with radii ρ < 2ρ), and let g(y) := constOfIsEmpty(ψ(y)), the 0-form with g(y)⟨⟩ = ψ(y); g is smooth with compact support, so g ∈ 𝒟⁰(ℝ^P). For y ∈ B_ρ(0), ψ = 1 on a neighbourhood of y, so Dψ(y) = 0 and dg(y) = ofSubsingleton(Dψ(y)) = 0 (extDeriv_constOfIsEmpty). Hence the support of dg lies in the closed set ℝ^P ∖ B_ρ(0), so tsupport(dg) is disjoint from B_ρ(0) ⊇ spt T, and ∂T(g) = T(dg) = 0 by (VO). On the other hand F ⊆ spt ∂T ⊆ spt T ⊆ B_ρ(0) by step 1, so g(x)⟨⟩ = 1 for x ∈ F and ∂T(g) = Σ_{x∈F} m(x). Hence Σ_{x∈F} m(x) = 0.
6. Segments. Put a := 0 ∈ ℝ^P. For each x ∈ ℝ^P choose, by segment_current (with (MR)), an integer multiplicity S_x ∈ 𝒟_1(ℝ^P) with ∂S_x(g) = g(x)⟨⟩ − g(a)⟨⟩ for all test 0-forms g, M(S_x) < ∞ and spt S_x ⊆ [a, x].
7. Combination. current_algebra (c), with (IMC)(c), U := ℝ^P (open), ι := ℝ^P, the finite set F, the currents S_x and the integers m(x), gives an integer multiplicity Y ∈ 𝒟_1(ℝ^P) with Y(ω) = Σ_{x∈F} m(x)S_x(ω) for all ω and M(Y) ≤ Σ_{x∈F}|m(x)|M(S_x) < ∞ (a finite sum of finite terms).
8. ∂Y = ∂T: for every test 0-form g, ∂Y(g) = Y(dg) = Σ_{x∈F} m(x)S_x(dg) = Σ_{x∈F} m(x)∂S_x(g) = Σ_{x∈F} m(x)g(x)⟨⟩ − (Σ_{x∈F} m(x))g(a)⟨⟩ = ∂T(g) by steps 4–6; hence ∂Y = ∂T (GeometricCurrentOn.ext).
9. spt Y is compact: C := ⋃_{x∈F}[a, x] is compact, being a finite union of segments, each the continuous image of [0, 1]. If tsupport ω ∩ C = ∅, then tsupport ω ∩ spt S_x = ∅ for each x ∈ F, so S_x(ω) = 0 by (VO) and Y(ω) = 0; support_vanish with K := C gives that spt Y is compact.
10. In both cases Y is integer multiplicity, ∂Y = ∂T, M(Y) < ∞ and spt Y is compact. ∎

## Key steps

1. spt ∂T ⊆ spt T is compact ((VO) and support_vanish).
2. d ≥ 1: (ISO) applied to the cycle ∂T; the filling lies in a bounded thickening, so its support is compact.
3. d = 0: ∂T = Σ m(x)δ_x over a finite F ⊆ spt T (zero_current_sum), and Σ m(x) = 0 by testing with a bump form equal to 1 near spt T and (VO).
4. Y := Σ m(x)[[0, x]] (segment_current, current_algebra (c)) is IM with ∂Y = ∂T, finite mass and compact support.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD (b4d606db1); cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical)`
- `rg -c 'dmcbr_cc|cbr_cc_' SNAPSHOT (no match, exit 1); rg -n -i 'segment current|slice property|integer slice|compact_im_filling|slice_property' SNAPSHOT/project/GMT -g '*.lean' (no match); rg -c '^theorem ' SNAPSHOT/project/GMT/Ch07/Contract.lean (1, main_theorem)`
- `rg -l -F over SNAPSHOT/mathlib/Mathlib and .lake/packages/simongmt/Poincare for names cited by the child proofs, all found: euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton, map_euclideanHausdorffMeasure, euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_eq_volume, integral_withDensity_eq_integral_smul, restrict_withDensity, withDensity_absolutelyContinuous, extDeriv_constOfIsEmpty, setIntegral_finset, integral_eq_sub_of_hasDerivAt, ae_lt_top, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero, ContDiffBump, segment_eq_image, Infinite.exists_subset_card_eq, sum_measure_singleton (a lemma in MeasureTheory/Measure/Basic.lean), integrableOn_singleton_iff, tsupport_exteriorDerivative_subset, GeometricCurrentOn.isOpen_zeroRegion`
- `sed on SimonGMT Chapter06/Currents.lean (GeometricCurrentOn, boundary, boundary_boundary, WeaklyConvergesOn.boundary), Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn, massOn_mono, WeaklyConvergesOn.massOn_le_liminf), Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, support), Chapter03/Rectifiable.lean (CountablyRectifiable, countablyRectifiable_range, CountablyRectifiable.mono, blowUpMap, HasApproximateTangentSpaceAt); GMT/Ch07/Contract.lean (IMRep, action, Represents, measure, IsIntegerMultiplicity, Sub instance, boundaryMassOn, CompactlyContained)`
- `python3 scans of RUN/dag.json: the selected type is byte-identical to the frozen type of the closure_compact node of the compactness branch (cbr_closure_compact_support), and the twelve child types of the two parents agree byte for byte; that node's eight children with their types, dependencies and accepted-checkpoint status; no node uses the prefix dmcbr_cc; the Lean names in the depends_on lists of all ancestors of the new children (none of them is cited in a child proof text)`
- `grep and sed in FLOW/_recursive_lean (FLOW = /runtime/flows/gmt-claude-0e9a4f203404): _existing_lean_name_problem, _accepted_checkpoint, Store.ensure, _install_parent_supplied_child_handoff, _render_parent_supplied_natural, _reference_use_problem, inherited.cited_inherited, decomposition_scope.scope (the binding digest 909f0f11... is reproduced)`
- `git show of the accepted commits 02c6122c94d0, 642d7450f79f, 791f7d722ecc, b4a337bf4785 (declared types of the four reused names are byte-identical; their lean-audit records have comparator_passed true) and of the speculative drafts e9fd47c2a312 (assembly of the identical node) and 32924cd7bc00 (filling)`
- `lake env lean (toolchain lean-4.35.0-rc3) on /tmp/dmcbr_cc_split/lean/Types.lean (all child, sibling and parent types elaborate after import GMT.Ch07.Submission in the replayed contract scope; sorry warnings only), Assembly.lean, Reused.lean and Fill.lean (#print axioms: propext, Classical.choice, Quot.sound); verifier lean_contract.validate_lean_statement on every type`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Segment.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-cf8c2c951f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-cf8c2c951f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b218e818f5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b218e818f5/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/decomposition_scope.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dmcbr_cc_split/lean/Types.lean`
- `/tmp/dmcbr_cc_split/lean/Assembly.lean`
- `/tmp/dmcbr_cc_split/lean/Reused.lean`
- `/tmp/dmcbr_cc_split/lean/Fill.lean`

Pins match: HEAD b4d606d equals the snapshot's project commit, Mathlib is 25730c7c, and Submission.lean is byte-identical to both the frozen contract and the snapshot copy. The snapshot has no dmcbr_cc or cbr_cc_ declaration and no segment-current, slicing or filling result. Every Mathlib and SimonGMT name cited by the child proofs exists in the pinned sources. The selected type is byte-identical to the compactness branch's closure_compact node, and its reviewed eight-child split is mirrored here. Four accepted declarations are reused with byte-identical types: rsd_cmr_support_subset_of_vanish, dtc_imrep_current, cbr_cc_current_algebra and cbr_cc_slice_property_sub. Their comparator passed, and their accepted proofs recompile with exactly propext, Classical.choice and Quot.sound. The four still-unaccepted counterparts get fresh, collision-free names with byte-identical types: dmcbr_cc_slice_property_of_im, dmcbr_cc_segment_current, dmcbr_cc_zero_current_finite_sum and dmcbr_cc_compact_im_filling. All eight types pass lexical validation and elaborate. The hypothesis-only assembly proves the exact selected type from them and the five sibling types with the same three axioms, and the filling type follows from its four declared sibling types. No child proof text cites an ancestor's dependency by Lean name, so no inherited prerequisite is added.
