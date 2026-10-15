# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_dilation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: paragraph (K) "Cone facts" of the parent proof of idtp_two_dim_cone_integer_density (Departure [D3] of that proof: the book, chapter-07.txt lines 497–510, gives no proof). Conventions: ℝ^P = Euclid P; B_r(x) = ball x r; for a current T on a domain D and W ⊆ ℝ^P, M_W(T) = T.massOn W is the supremum in [0, ∞] of ofReal(T(ω)) over ω ∈ 𝒟^n(D) (test forms with tsupport ω ⊆ D) such that tsupport ω ⊆ W and covectorEuclideanNorm(ω(y)) ≤ 1 for all y; ω_n = unitBallVolume n; η_{x,λ} = dilation x λ, η_{x,λ}(y) = −(λ⁻¹x) + λ⁻¹y.
1. Fix s > 0 and let λ := s⁻¹ > 0. Then η_{0,λ}(y) = −(λ⁻¹·0) + λ⁻¹y = s·y for every y. Hence η_{0,λ}(W) = sW for every W ⊆ ℝ^P, and D := η_{0,λ}(ℝ^P) = ℝ^P, because every y equals η_{0,λ}(s⁻¹y). Let B := blowUp C 0 λ ∈ 𝒟_n(D).
2. (B and C have the same local masses.) Let V ⊆ ℝ^P. The elements of 𝒟^n(D) are the forms ω with IsTestForm ω and tsupport ω ⊆ D = ℝ^P; these are exactly the underlying forms of the elements of 𝒟^n(ℝ^P), and the admissibility conditions defining M_V (tsupport ω ⊆ V and covectorEuclideanNorm(ω(y)) ≤ 1 for all y) depend only on the underlying form. For such an ω the condition IsTestForm ω ∧ tsupport ω ⊆ D holds, so currentEval(B, ω) = B(ω) by the definition of currentEval, and IsConeCurrent C (for this λ > 0) gives currentEval(B, ω) = C(ω). Hence the sets {ofReal(B(ω))} and {ofReal(C(ω))}, ω ranging over the M_V-admissible forms, are equal, and M_V(B) = M_V(C) for every V ⊆ ℝ^P.
3. (Conclusion (1).) The accepted theorem Submission.dtc_blowUp_massOn_image (U := ℝ^P, T := C, x := 0, lam := λ, and the given W) gives M_{η_{0,λ}(W)}(B) = ofReal((λ⁻¹)^n)·M_W(C). By step 1, η_{0,λ}(W) = sW and λ⁻¹ = s; by step 2, M_{sW}(B) = M_{sW}(C). Therefore M_{sW}(C) = ofReal(s^n)·M_W(C).
4. (Balls.) For x ∈ ℝ^P and r > 0, s·B_{r/s}(x) = B_r(s·x): |s·y − s·x| = s|y − x| < r if and only if |y − x| < r/s, and every z ∈ B_r(s·x) equals s·(s⁻¹z) with s⁻¹z ∈ B_{r/s}(x). By (1), M_{B_r(s·x)}(C) = ofReal(s^n)·M_{B_{r/s}(x)}(C), and ofReal(s^n) ∈ (0, ∞).
5. (Conclusion (2).) Choose an IMRep R of ℝ^P with R.Represents C (IsIntegerMultiplicity C) and let μ := R.measure. The accepted theorem Submission.dimred_im_mass_measure (U := ℝ^P, which is open, T := C) gives (a) M_W(C) = μ(W) for every open W ⊆ ℝ^P, and (b) y ∈ spt C if and only if μ(B_ε(y)) ≠ 0 for every ε > 0. By step 4 and (a), μ(B_r(s·x)) = ofReal(s^n)·μ(B_{r/s}(x)) for every r > 0; since ofReal(s^n) ∈ (0, ∞), μ(B_r(s·x)) ≠ 0 if and only if μ(B_{r/s}(x)) ≠ 0. As r runs through (0, ∞), so does r/s. By (b), s·x ∈ spt C if and only if x ∈ spt C.
6. (Conclusion (3).) For ρ > 0 let f(ρ) := M_{B_ρ(s·x)}(C)/(ω_n·ofReal(ρ^n)) and g(ρ) := M_{B_ρ(x)}(C)/(ω_n·ofReal(ρ^n)). Since ρ^n = s^n·(ρ/s)^n with both factors ≥ 0, ofReal(ρ^n) = ofReal(s^n)·ofReal((ρ/s)^n). By step 4 and cancellation of the common factor ofReal(s^n) ∈ (0, ∞) in numerator and denominator (ENNReal.mul_div_mul_left), f(ρ) = g(ρ/s) for every ρ > 0, and likewise g(t) = f(s·t) for every t > 0. The maps ρ ↦ ρ/s and t ↦ s·t send the filter 𝓝[>]0 into 𝓝[>]0. Hence, for every θ, f tends to ofReal θ along 𝓝[>]0 if and only if g does. Since HasMassDensity C y θ means 0 ≤ θ together with the convergence of the corresponding ratio at y to ofReal θ, HasMassDensity C (s·x) θ holds if and only if HasMassDensity C x θ holds. ∎

## Key steps

1. With λ = 1/s, dilation 0 λ is y ↦ s·y and maps ℝ^P onto ℝ^P.
2. The cone identity makes blowUp C 0 λ and C agree on every admissible test form, so M_V(blowUp C 0 λ) = M_V(C) for all V.
3. Submission.dtc_blowUp_massOn_image then gives M_{sW}(C) = s^n·M_W(C), in particular M_{B_r(sx)}(C) = s^n·M_{B_{r/s}(x)}(C).
4. Mass equals the representation measure μ on open sets and spt C = {y : μ(B_ε(y)) ≠ 0 for all ε > 0} (dimred_im_mass_measure), giving sx ∈ spt C ⟺ x ∈ spt C.
5. The density ratio at sx and radius ρ equals the ratio at x and radius ρ/s, so the densities coincide.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `sed -n 1,140p simongmt Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean; sed -n 20,100p Chapter06/Mass.lean; sed -n 30,135p,305,340p Chapter06/Currents.lean; sed -n 36,60p Chapter06/Forms.lean`
- `grep -rn 'μHE\[' mathlib/Mathlib (notation and API in Geometry/Euclidean/Volume/Measure.lean)`
- `rg -n 'theorem isConnected_sphere|theorem isConnected_compl_singleton_of_one_lt_rank|theorem addHaar_ball |theorem addHaar_ball_of_pos|theorem hausdorffMeasure_zero_singleton|theorem ext_of_generateFrom_of_iUnion|theorem mul_le_sin|theorem closed_of_finiteDimensional|theorem isCompact_sphere|measure_compl_support' mathlib/Mathlib`
- `rg -n 'closed_of_finiteDimensional|class OuterRegular|of_pseudoMetrizableSpace_of_isFiniteMeasure|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|exists_isOpen_lt_of_lt' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n 'measurePreserving' Haar/InnerProductSpace.lean; rg -n 'volume_ball' Lebesgue/VolumeOfBalls.lean; rg -n 'theorem isOpen_iUnion_countable|theorem cos_arg|theorem sin_arg|theorem euclideanHausdorffMeasure_preimage|theorem Orthonormal.linearIndependent' mathlib/Mathlib`
- `python3 scan of dag.json: lean_name collisions for the seven idtp_tdc_* names (none among 817 nodes); exact types and statuses of idtp_cone_tangent_cone_planar, idtp_cone_constant_density_planar, idtp_cone_sector_endpoint_density, idtp_planar_cycle_eq_const_mul, dimred_minimizing_monotonicity, dimred_im_mass_measure, dtc_blowUp_massOn_image, dtc_restrictDomain_isIntegerMultiplicity, cone_current_imrep_measure_smul_image, dtc_density_usc, rsd_massOn_eq_measure, rsd_mem_support_iff_measure_ball_pos, codim1_subspace_ball_euclideanHausdorff`
- `grep for idtp_tdc_ in nodes/*/*.json and workspaces/*/GMT (no match)`
- `sed -n 480,520p book/chapter-07.txt`
- `lake env lean /tmp/tdcd-split-a1/gen/Child_<key>.lean for each of the 7 children; lake env lean /tmp/tdcd-split-a1/gen/Assembly.lean (#print axioms tdc_assembly_check); lake env lean /tmp/tdcd-split-a1/gen/Probe.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Connected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-edecc539dd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/tdcd-split-a1/gen/Assembly.lean`
- `/tmp/tdcd-split-a1/gen/Probe.lean`
- `/tmp/tdcd-split-a1/gen/Child_cone_dilation.lean`
- `/tmp/tdcd-split-a1/gen/Child_subspace_ball_measure.lean`
- `/tmp/tdcd-split-a1/gen/Child_no_infinite_planar_pieces.lean`
- `/tmp/tdcd-split-a1/gen/Child_arc_continuation.lean`
- `/tmp/tdcd-split-a1/gen/Child_density_locally_constant.lean`
- `/tmp/tdcd-split-a1/gen/Child_cone_set_finite_planes.lean`
- `/tmp/tdcd-split-a1/gen/Child_planes_union_vertex_density.lean`

Pins and contract:
- The pins match manifest.json: project b4d606db, mathlib 25730c7c, SimonGMT 2b366308.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

SimonGMT Chapter06 definitions used by the children:
- support = U \ zeroRegion with zeroRegion open, so spt C is closed when U = univ.
- restrictDomain, massOn (sSup over admissible test forms), boundary and TestFormOn (IsTestForm ∧ tsupport ⊆ U).

Mathlib snapshot: it contains every library fact the child proofs cite:
- Isometry.euclideanHausdorffMeasure_preimage, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_zero_or_top, euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton.
- Measure.addHaar_ball_of_pos (no Nontrivial hypothesis), LinearIsometryEquiv.measurePreserving.
- isConnected_sphere, isConnected_compl_singleton_of_one_lt_rank, Submodule.closed_of_finiteDimensional, isCompact_sphere.
- Measure.ext_of_generateFrom_of_iUnion, WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure, Set.exists_isOpen_lt_of_lt, isOpen_iUnion_countable, Real.mul_le_sin, Complex.cos_arg/sin_arg.

Reuse:
- No accepted DAG declaration has the exact type of any proposed child. codim1_subspace_ball_euclideanHausdorff is closest, but it is not accepted and is centred at 0. cone_current_imrep_measure_smul_image is accepted but states something different.
- Seven new idtp_tdc_* names are therefore used. None occurs in dag.json (817 nodes), in any node JSON file, or in the workspace GMT sources.
- The cited black boxes have their frozen DAG types and elaborate (Probe.lean). dimred_im_mass_measure, dtc_blowUp_massOn_image and dtc_restrictDomain_isIntegerMultiplicity are accepted. dimred_minimizing_monotonicity is in progress, and the parent's own proof already cites it.

Lean checks:
- All seven exact lean_statement strings elaborate after import GMT.Ch07.Submission, each in its own file.
- The hypothesis-only assembly derives the exact selected type idtp_two_dim_cone_integer_density. It uses children cone_dilation, density_locally_constant, cone_set_finite_planes and planes_union_vertex_density, plus the frozen type of idtp_cone_constant_density_planar taken from dag.json. Its axioms are propext, Classical.choice and Quot.sound.
