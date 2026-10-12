# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.local_isolating_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 2–6 (coordinate covector, separation of parallel faces, evaluation formula, positive bump at an interior point, approximation of a face point by interior points), specialized to produce one localized test form. The separation of step 3 is supplied by the accepted cut-off isoperimetric_lattice_face_cutoff, which the parent's Remark allows: that cut-off vanishes on all other faces of direction α₀, which is all step 4 uses.

Notation.
- F₀ = (z, α) and A := range α.
- e_a := EuclideanSpace.single a 1; H := μHE[n] on ℝ^N.
- dx^α := wedgeCovectors n (i ↦ EuclideanSpace.proj (α i)).
- [[F]](ω) := latticeFaceAction ρ F ω.
- For δ > 0, K_δ := {y : ρ(z_i + δ) ≤ y_i ≤ ρ(z_i + 1 − δ) (i ∈ A), y_i = ρz_i (i ∉ A)}.
- Hypotheses: ρ > 0; x ∈ latticeFace ρ F₀, i.e. ρz_i ≤ x_i ≤ ρ(z_i + 1) for i ∈ A and x_i = ρz_i for i ∉ A; W open; x ∈ W.

1. Centre. Let c ∈ ℝ^N with c_i := ρ(z_i + 1/2) for i ∈ A and c_i := ρz_i for i ∉ A.
2. A nearby point. The map t ↦ x + t(c − x), ℝ → ℝ^N, is continuous and sends 0 to x ∈ W. So the preimage of the open set W is open and contains 0, and there is ε > 0 with x + t(c − x) ∈ W whenever |t| < ε (Metric.isOpen_iff). Let t := min(ε/2, 1). Then 0 < t ≤ 1 and t < ε, so p := x + t(c − x) ∈ W. Coordinatewise, p_i = x_i + t(c_i − x_i).
3. p ∈ K_{t/2}.
 - For i ∈ A: p_i − ρ(z_i + t/2) = (1 − t)(x_i − ρz_i) ≥ 0 and ρ(z_i + 1 − t/2) − p_i = (1 − t)(ρ(z_i + 1) − x_i) ≥ 0. This uses c_i = ρ(z_i + 1/2), 0 < t ≤ 1 and ρz_i ≤ x_i ≤ ρ(z_i + 1).
 - For i ∉ A: x_i = c_i = ρz_i, so p_i = ρz_i.
 Consequently p is a relative-interior point of the face: for i ∈ A, ρz_i < ρ(z_i + t/2) ≤ p_i ≤ ρ(z_i + 1 − t/2) < ρ(z_i + 1), because ρt/2 > 0; and p_i = ρz_i for i ∉ A.
4. Bump. W is a neighbourhood of p. By exists_contDiff_tsupport_subset (ℝ^N is finite-dimensional; smoothness ⊤ : ℕ∞) there is ψ : ℝ^N → ℝ, C^∞, with compact support, tsupport ψ ⊆ W, range ψ ⊆ [0, 1] and ψ(p) = 1.
5. Cut-off. Apply sibling face_cutoff (isoperimetric_lattice_face_cutoff) with δ := t/2 > 0, z and α. It gives φ : ℝ^N → ℝ that is C^∞, compactly supported, with 0 ≤ φ ≤ 1, φ = 1 on K_{t/2} (so φ(p) = 1 by step 3), and φ(y) = 0 for every y ∈ latticeFace ρ (z', α) with z' ≠ z.
6. Covector. Apply sibling coord_covector (isoperimetric_coord_covector_eval n N α): dx^α(e_{α(0)}, …, e_{α(n−1)}) = 1, and dx^α(e_{α'(0)}, …, e_{α'(n−1)}) = 0 for every α' ∈ SimonMultiIndex n N with α' ≠ α.
7. The form. Let g := ψ·φ (pointwise product).
 - g is C^∞ as a product of C^∞ functions, has compact support because ψ does (HasCompactSupport.mul_right), satisfies g ≥ 0, and g(p) = ψ(p)φ(p) = 1.
 - Define ω(y) := g(y) • dx^α. It is C^∞ (a smooth scalar times a constant covector), has compact support (HasCompactSupport.smul_right) and tsupport ω ⊆ univ. So ω ∈ TestFormOn univ n, and ω(y)(v) = g(y)·dx^α(v).
 - tsupport ω ⊆ tsupport g ⊆ tsupport ψ ⊆ W (tsupport_smul_subset_left, tsupport_mul_subset_left, step 4). This is property (1).
8. Other faces. Let F = (z', α') ≠ F₀.
 - If α' = α, then z' ≠ z. For y ∈ latticeFace ρ F the integrand is ψ(y)φ(y)·dx^α(e_α) = 0, since φ(y) = 0 by step 5. A set integral of a function vanishing on the set is 0 (setIntegral_eq_zero_of_forall_eq_zero).
 - If α' ≠ α, the integrand is g(y)·dx^α(e_{α'}) = 0 for all y by step 6, so the integral is 0.
 Hence [[F]](ω) = 0, which is property (2).
9. The face F₀. By step 6, [[F₀]](ω) = ∫_{latticeFace ρ F₀} g(y)·1 dH(y) = ∫_{latticeFace ρ F₀} g dH. Apply sibling face_integral_pos to (n, N, ρ, F₀, g, p). Its hypotheses hold: ρ > 0; g is continuous (being C^∞); g ≥ 0; g(p) = 1 > 0; and p satisfies the relative-interior condition by step 3. Hence [[F₀]](ω) > 0, which is property (3). ∎

Remark (optional, not part of the argument): this Lean text compiled in a scratch copy of the project (Lean v4.35.0-rc3, Mathlib 25730c7c) with the accepted Submission.isoperimetric_lattice_face_cutoff, Submission.isoperimetric_coord_covector_eval and the sibling Submission.fiw_tb_lcc_face_integral_pos available; #print axioms gives [propext, Classical.choice, Quot.sound].

theorem Submission.fiw_tb_lcc_local_isolating_form : ∀ (n N : ℕ) (ρ : ℝ) (F₀ : LatticeFaceIndex n N) (x : Eucl N) (W : Set (Eucl N)), 0 < ρ → x ∈ latticeFace ρ F₀ → IsOpen W → x ∈ W → ∃ ω : TestFormOn (univ : Set (Eucl N)) n, tsupport (ω : DifferentialForm (Eucl N) n) ⊆ W ∧ (∀ F : LatticeFaceIndex n N, F ≠ F₀ → latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧ 0 < latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n) := by
  intro n N ρ F₀ x W hρ hx hW hxW
  obtain ⟨z, α⟩ := F₀
  -- Step 1: the centre `c` of the face.
  set c : Eucl N := WithLp.toLp 2 (fun i => if i ∈ range α then ρ * ((z i : ℝ) + 1 / 2)
    else ρ * (z i : ℝ)) with hc
  -- Step 2: a point `p = x + t (c - x)`, `0 < t ≤ 1`, of `W`.
  have hcont : Continuous fun t : ℝ => x + t • (c - x) := by fun_prop
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => x + t • (c - x)) ⁻¹' W := by simpa using hxW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hW.preimage hcont) 0 h0
  set t : ℝ := min (ε / 2) 1 with ht
  have ht0 : 0 < t := lt_min (half_pos hε) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  set p : Eucl N := x + t • (c - x) with hp
  have hpW : p ∈ W := hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htε)
  have hpcoord : ∀ i, p i = x i + t * (c i - x i) := fun i => by simp [hp]
  -- Step 3: `p` lies in the shrunken face `K_{t/2}`, hence in the open face.
  have hpK : ∀ i : Fin N, (i ∈ range α → ρ * ((z i : ℝ) + t / 2) ≤ p i ∧
      p i ≤ ρ * ((z i : ℝ) + 1 - t / 2)) ∧ (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    constructor
    · intro hi
      obtain ⟨h1, h2⟩ := (hx i).1 hi
      have hci : c i = ρ * ((z i : ℝ) + 1 / 2) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci]
      constructor <;> nlinarith
    · intro hi
      have hci : c i = ρ * (z i : ℝ) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci, (hx i).2 hi]
      ring
  have hpopen : ∀ i : Fin N, (i ∈ range α → ρ * (z i : ℝ) < p i ∧ p i < ρ * ((z i : ℝ) + 1)) ∧
      (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    refine ⟨fun hi => ?_, (hpK i).2⟩
    obtain ⟨h1, h2⟩ := (hpK i).1 hi
    constructor <;> nlinarith
  -- Step 4: a bump `ψ` at `p` supported in `W`, the cut-off `φ` of the face, `dx^α`.
  obtain ⟨ψ, hψW, hψc, hψs, hψr, hψp⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hW.mem_nhds hpW)
  obtain ⟨φ, hφs, hφc, hφ01, hφ1, hφ0⟩ :=
    Submission.isoperimetric_lattice_face_cutoff n N ρ (t / 2) z α hρ (half_pos ht0)
  obtain ⟨hηα, hηne, -⟩ := Submission.isoperimetric_coord_covector_eval n N α
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i))
  -- Step 5: the test form `ω = (ψ φ) • dx^α`.
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ψ y * φ y) := hψs.mul hφs
  have hgc : HasCompactSupport (fun y => ψ y * φ y) := hψc.mul_right
  obtain ⟨ω, hωx⟩ : ∃ ω : TestFormOn (univ : Set (Eucl N)) n,
      ∀ y, (ω : DifferentialForm (Eucl N) n) y = (ψ y * φ y) • η :=
    ⟨⟨fun y => (ψ y * φ y) • η, ⟨hgs.smul contDiff_const, hgc.smul_right (f' := fun _ => η)⟩,
      subset_univ _⟩, fun _ => rfl⟩
  have hωv : ∀ y (v : Fin n → Eucl N), (ω : DifferentialForm (Eucl N) n) y v = ψ y * φ y * η v :=
    fun y v => by rw [hωx, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine ⟨ω, ?_, ?_, ?_⟩
  -- Step 6: `tsupport ω ⊆ tsupport ψ ⊆ W`.
  · have hω : (ω : DifferentialForm (Eucl N) n) = fun y => (ψ y * φ y) • η := funext hωx
    rw [hω]
    exact (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left.trans hψW)
  -- Step 7: every other face contributes `0`.
  · rintro ⟨z', α'⟩ hF
    rw [latticeFaceAction]
    by_cases hα : α' = α
    · have hz : z' ≠ z := fun h => hF (by rw [h, hα])
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [hωv, hφ0 z' hz y (by rwa [hα] at hy), mul_zero, zero_mul]
    · simp only [hωv, hηne α' hα, mul_zero, integral_zero]
  -- Step 8: `[[F₀]](ω) = ∫_{F₀} ψ φ dHⁿ > 0`.
  · have hval : latticeFaceAction ρ ((z, α) : LatticeFaceIndex n N) (ω : DifferentialForm (Eucl N) n) =
        ∫ y in latticeFace ρ ((z, α) : LatticeFaceIndex n N), ψ y * φ y ∂(μHE[n] : Measure (Eucl N)) := by
      simp only [latticeFaceAction, hωv, hηα, mul_one]
    rw [hval]
    refine Submission.fiw_tb_lcc_face_integral_pos n N ρ (z, α) (fun y => ψ y * φ y) p hρ
      hgs.continuous (fun y => mul_nonneg (hψr ⟨y, rfl⟩).1 (hφ01 y).1) ?_ hpopen
    rw [hψp, hφ1 p hpK, one_mul]
    exact one_pos

## Key steps

1. Move x toward the face centre c: p = x + t(c − x) lies in W for some t ∈ (0,1].
2. p lies in the shrunken face K_{t/2}, hence in the relative interior of F₀.
3. Take a bump ψ at p with tsupport ψ ⊆ W and ψ(p) = 1, and the cut-off φ (1 on K_{t/2}, 0 on the other faces of direction α).
4. ω = (ψφ) dx^α is a test form on ℝ^N with tsupport ω ⊆ W.
5. dx^α kills faces of other directions and φ kills the parallel faces, so [[F]](ω) = 0 for F ≠ F₀.
6. [[F₀]](ω) = ∫_{F₀} ψφ dH^n > 0 by face_integral_pos (ψφ is continuous, nonnegative and equals 1 at p).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (snapshot = .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494): mode local-project, project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d`
- `rg -n 'latticeFaceAction|IsLatticeChain|zeroRegion|latticeFace ' <snapshot>/project`
- `rg -n 'isoperimetric_lattice_chain_mass_ge|fiw_tb_lcc|local_isolating|face_integral_pos|lattice_face_cutoff' <snapshot>/project (no match, rc=1)`
- `rg in <snapshot>/mathlib/Mathlib: 'theorem exists_contDiff_tsupport_subset', 'theorem setIntegral_pos_iff_support_of_nonneg_ae', 'theorem _root_.IsOpen.measure_pos', 'theorem isOpen_set_pi', 'Continuous.isOpen_mulSupport', 'tprod_eq_mulSingle', 'theorem HasCompactSupport.mul_right', 'theorem tsupport_smul_subset_left', 'theorem tsupport_mul_subset_left', 'theorem setIntegral_eq_zero_of_forall_eq_zero', 'theorem isOpen_iff', 'theorem ContinuousOn.integrableOn_compact'`
- `python3 -I scan of dag.json: lean_name/lean_statement/status/candidate_commit of isoperimetric_lattice_chain_mass_ge, isoperimetric_coord_covector_eval, isoperimetric_lattice_face_cutoff, br_latticeFace_setIntegral_eq_cube; search for lean_names containing fiw_tb_lcc / local_isolating / face_integral_pos`
- `git log --all --oneline -S fiw_tb_lcc_ (no match)`
- `git show b1a770c375be212de585c186965d7d1f653fb13a:GMT/Ch06/Submission.lean ; git show 0561b355216f4041a30f4aaf2a4b139abdf038ca:GMT/Ch06/Submission.lean`
- `grep -n 'def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support|def GeometricCurrentOn.VanishesOn|def massAdmissibleOn|theorem GeometricCurrentOn.le_massOn|theorem covectorEuclideanNorm_neg|abbrev TestFormOn|structure GeometricCurrentOn' in SimonGMT Chapter06`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|_install_parent_supplied_child_handoff|def ensure' /runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py store.py`
- `lake build Scratch.Acc; lake env lean Scratch/Pos.lean, Scratch/Iso.lean, Scratch/All.lean (#print axioms) in /tmp/lcc-scratch-Z3tV82`
- `python3 -I /tmp/lcc-tools/gen_challenges.py and gen_solutions.py (verifier/gmt-compare.py child_modules contract mode + lean_contract.validate_lean_statement); lake env lean Scratch/Ch_*.lean and Scratch/NodeSolution_*.lean`
- `sed -n 2028,2095p book/chapter-06.txt (Simon 7.2 proof, display (2): Σ_F |β_F| ρ^n ≤ c M(T))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/lcc-scratch-Z3tV82/Scratch/Acc.lean`
- `/tmp/lcc-scratch-Z3tV82/Scratch/All.lean`

Pinned snapshot: project d8d46c95, Mathlib 25730c7c.
- Its project tree holds only the frozen Ch06 contract (latticeFace, latticeFaceAction, IsLatticeChain). Submission.lean is a byte copy.
- A search for a lattice-chain coefficient or support lemma, or for the proposed new names, finds nothing (rc=1).
- The accepted Submission declarations live in run commits. dag.json shows four of them are accepted and have exactly the needed frozen types:
  - isoperimetric_lattice_chain_mass_ge @ b1a770c3, the whole of part (b);
  - isoperimetric_coord_covector_eval @ 3d98b187;
  - isoperimetric_lattice_face_cutoff @ b27494a6;
  - br_latticeFace_setIntegral_eq_cube @ 0561b355.
  They are reused, and their proofs are reproduced from git show.
- SimonGMT supplies zeroRegion, support (= U \ zeroRegion), VanishesOn, TestFormOn and le_massOn.
- The Mathlib snapshot supplies every lemma the new children use:
  - exists_contDiff_tsupport_subset (FiniteDimension.lean:45);
  - setIntegral_pos_iff_support_of_nonneg_ae (Bochner/Set.lean:633);
  - IsOpen.measure_pos (OpenPos.lean:47);
  - isOpen_set_pi (Constructions.lean:1072);
  - Continuous.isOpen_support, the to_additive form of Continuous.isOpen_mulSupport (Separation/Basic.lean:383);
  - tsum_eq_single, the to_additive form of tprod_eq_mulSingle (InfiniteSum/Basic.lean:495);
  - HasCompactSupport.mul_right / smul_right (Support.lean:477/466);
  - tsupport_smul_subset_left / tsupport_mul_subset_left (Support.lean:168/124);
  - Metric.isOpen_iff (Pseudo/Defs.lean:833);
  - ContinuousOn.integrableOn_compact (LocallyIntegrable.lean:592).
- Scratch builds confirm all child types elaborate in the comparator scope. They also confirm that the new children and the parent assembly are provable with only propext, Classical.choice and Quot.sound.
