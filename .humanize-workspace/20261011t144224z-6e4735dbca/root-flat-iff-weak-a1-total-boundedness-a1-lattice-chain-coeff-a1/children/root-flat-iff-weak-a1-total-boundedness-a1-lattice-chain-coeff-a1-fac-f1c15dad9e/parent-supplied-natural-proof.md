# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.face_integral_pos-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, specialized to an arbitrary continuous nonnegative g:
- step 1 (parametrization ι of the face, with ι((0, ρ)^n) the relative interior);
- the positivity argument of step 5: '∫_{F_0} ψ dH = ∫_{[0,ρ]^n} ψ(ι(y)) dy > 0, because ψ∘ι is continuous and ≥ 0 and is > 0 at ι⁻¹(p) ∈ (0, ρ)^n, hence on a small ball inside [0, ρ]^n of positive Lebesgue measure'.

Notation.
- F = (z, α) and A := range α.
- e_l := EuclideanSpace.single l 1 ∈ ℝ^N; H := μHE[n] on ℝ^N.
- ℝ^n := Fin n → ℝ with Lebesgue measure volume.
- C := Icc 0 (fun _ => ρ) = {s : 0 ≤ s_j ≤ ρ for all j}; Q := {s : 0 < s_j < ρ for all j} = Set.pi univ (fun _ => Ioo 0 ρ).
- (H_p) is the hypothesis on p: ρz_i < p_i < ρ(z_i + 1) for i ∈ A, and p_i = ρz_i for i ∉ A.

1. Parametrization. Apply sibling face_param (br_latticeFace_setIntegral_eq_cube with P := N, d := n, G := F and our g). It gives ∫_{latticeFace ρ F} g dH = ∫_C h(s) ds, where ι(s) := Σ_l ρ z_l e_l + Σ_j s_j e_{α(j)} and h := g ∘ ι : ℝ^n → ℝ.
2. Regularity. ι is continuous: a constant plus a finite sum of the continuous maps s ↦ s_j • e_{α(j)}. So h = g ∘ ι is continuous, and h ≥ 0 because g ≥ 0.
3. Coordinates of ι. For l ∈ Fin N, ι(s)_l = ρz_l + Σ_j [l = α(j)] s_j (EuclideanSpace.single_apply). Since α is injective, ι(s)_{α(j)} = ρz_{α(j)} + s_j, and ι(s)_l = ρz_l for l ∉ A.
4. The base point. Put s₀_j := p_{α(j)} − ρz_{α(j)} for j ∈ Fin n.
 - By (H_p) at i = α(j) ∈ A, 0 < s₀_j < ρ, so s₀ ∈ Q.
 - By step 3, ι(s₀)_{α(j)} = p_{α(j)}, and for l ∉ A, ι(s₀)_l = ρz_l = p_l by (H_p).
 Hence ι(s₀) = p and h(s₀) = g(p) > 0.
5. Reduction to a measure. C is compact and h is continuous, so h is integrable on C (ContinuousOn.integrableOn_compact). Since h ≥ 0 everywhere (in particular a.e. on C), setIntegral_pos_iff_support_of_nonneg_ae gives: 0 < ∫_C h ⟺ 0 < volume(support h ∩ C).
6. Positive measure. Let V := support h ∩ Q.
 - V is open: support h = h⁻¹(ℝ ∖ {0}) is open since h is continuous (Continuous.isOpen_support), and Q is a finite product of open intervals (isOpen_set_pi).
 - V is nonempty: s₀ ∈ V by step 4.
 - Lebesgue measure on ℝ^n is positive on nonempty open sets (IsOpen.measure_pos), so volume(V) > 0. For n = 0, ℝ^0 is one point of measure 1 and Q is all of it, so this case is covered by the same argument.
7. Conclusion. Since Q ⊆ C, V ⊆ support h ∩ C, so volume(support h ∩ C) ≥ volume(V) > 0 (measure_mono). By steps 5 and 1, 0 < ∫_C h = ∫_{latticeFace ρ F} g dH. ∎

Remark (optional, not part of the argument): this Lean text compiled in a scratch copy of the project (Lean v4.35.0-rc3, Mathlib 25730c7c) with the accepted Submission.br_latticeFace_setIntegral_eq_cube available; #print axioms gives [propext, Classical.choice, Quot.sound].

theorem Submission.fiw_tb_lcc_face_integral_pos : ∀ (n N : ℕ) (ρ : ℝ) (F : LatticeFaceIndex n N) (g : Eucl N → ℝ) (p : Eucl N), 0 < ρ → Continuous g → (∀ x, 0 ≤ g x) → 0 < g p → (∀ i : Fin N, (i ∈ range F.2 → ρ * (F.1 i : ℝ) < p i ∧ p i < ρ * ((F.1 i : ℝ) + 1)) ∧ (i ∉ range F.2 → p i = ρ * (F.1 i : ℝ))) → 0 < ∫ x in latticeFace ρ F, g x ∂(μHE[n] : Measure (Eucl N)) := by
  intro n N ρ F g p hρ hg hg0 hgp hp
  rw [Submission.br_latticeFace_setIntegral_eq_cube N n ρ F g]
  -- the affine parametrization of the face
  set ι : (Fin n → ℝ) → Eucl N := fun s =>
    ∑ l, (ρ * (F.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) +
      ∑ j, s j • EuclideanSpace.single (F.2 j) (1 : ℝ) with hι
  have hιc : Continuous ι := by
    rw [hι]
    fun_prop
  have hcoord : ∀ (s : Fin n → ℝ) (l : Fin N),
      ι s l = ρ * (F.1 l : ℝ) + ∑ j, if l = F.2 j then s j else 0 := by
    intro s l
    simp [hι, Pi.single_apply]
  set s₀ : Fin n → ℝ := fun j => p (F.2 j) - ρ * (F.1 (F.2 j) : ℝ) with hs₀
  have hιs₀ : ι s₀ = p := by
    ext l
    rw [hcoord]
    by_cases hl : l ∈ range F.2
    · obtain ⟨j, rfl⟩ := hl
      simp [hs₀, F.2.injective.eq_iff]
    · have hne : ∀ j, l ≠ F.2 j := fun j h => hl ⟨j, h.symm⟩
      simp [hne, (hp l).2 hl]
  have hs₀mem : s₀ ∈ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ) := by
    intro j _
    obtain ⟨h1, h2⟩ := (hp (F.2 j)).1 ⟨j, rfl⟩
    constructor <;> simp only [hs₀] <;> linarith
  have hh : Continuous fun s => g (ι s) := hg.comp hιc
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun s => hg0 _)
    (hh.continuousOn.integrableOn_compact isCompact_Icc)]
  have hopen : IsOpen (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)) :=
    hh.isOpen_support.inter (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
  have hne : (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)).Nonempty :=
    ⟨s₀, by simp only [Function.mem_support, hιs₀]; exact hgp.ne', hs₀mem⟩
  calc (0 : ℝ≥0∞) < volume (Function.support (fun s => g (ι s)) ∩ Set.pi univ (fun _ => Ioo (0 : ℝ) ρ)) :=
        hopen.measure_pos volume hne
    _ ≤ volume (Function.support (fun s => g (ι s)) ∩ Icc (0 : Fin n → ℝ) (fun _ => ρ)) := by
        refine measure_mono (inter_subset_inter_right _ fun s hs => ⟨fun j => ?_, fun j => ?_⟩)
        · exact (hs j (mem_univ j)).1.le
        · exact (hs j (mem_univ j)).2.le

## Key steps

1. Rewrite the face integral as ∫_{[0,ρ]^n} g(ι(s)) ds using face_param.
2. h = g∘ι is continuous, nonnegative, and integrable on the compact cube.
3. s₀ = (p_{α(j)} − ρz_{α(j)})_j lies in the open cube (0,ρ)^n and ι(s₀) = p, so h(s₀) = g(p) > 0.
4. support h ∩ (0,ρ)^n is open and nonempty, so it has positive Lebesgue measure.
5. setIntegral_pos_iff_support_of_nonneg_ae turns this into a positive integral.

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
