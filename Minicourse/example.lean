import Mathlib

namespace Exercise_6245

/-
Let $F=\mathbb{Z}_{7}$ and let $p(x)=x^{3}-2$ and $q(x)=x^{3}+2$ be in $F[x]$. Show that $p(x)$ and $q(x)$ are irreducible in $F[x]$ and that the fields $F[x] /(p(x))$ and $F[x] /(q(x))$ are isomorphic.
-/

local notation "F" => ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Field F := ZMod.instField 7

open Polynomial

local notation "p" => X ^ 3 + C (- 2 : F)
local notation "q" => X ^ 3 + C (2 : F)

lemma p_natDegree : natDegree p = 3 := by compute_degree!
lemma q_natDegree : natDegree q = 3 := by compute_degree!

lemma irr_p : Irreducible p := by
  refine (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three ?_ ?_).2 ?_
  · rw [p_natDegree]; omega
  · rw [p_natDegree]
  · refine Multiset.eq_zero_iff_forall_not_mem.mpr ?_
    intro a
    simp only [map_neg, mem_roots', ne_eq, IsRoot.def, eval_add, eval_pow, eval_X, eval_neg, eval_C,
      not_and]
    rintro -
    fin_cases a
    all_goals simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_add, neg_eq_zero, Fin.mk_one, one_pow, Fin.reduceFinMk]; decide

lemma irr_q : Irreducible q := by
  refine (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three ?_ ?_).2 ?_
  · rw [q_natDegree]; omega
  · rw [q_natDegree]
  · refine Multiset.eq_zero_iff_forall_not_mem.mpr ?_
    intro a
    simp only [map_neg, mem_roots', ne_eq, IsRoot.def, eval_add, eval_pow, eval_X, eval_neg, eval_C,
      not_and]
    rintro -
    fin_cases a
    all_goals simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_add, neg_eq_zero, Fin.mk_one, one_pow, Fin.reduceFinMk]; decide

noncomputable section

instance fie₁ : Field (F[X] ⧸ Ideal.span {p}) := by
  refine IsField.toField ?_
  refine (Ideal.Quotient.maximal_ideal_iff_isField_quotient (Ideal.span {p})).1 ?_
  have _ : Fact (Irreducible p) := ⟨irr_p⟩
  exact AdjoinRoot.span_maximal_of_irreducible

instance fie₂ : Field (F[X] ⧸ Ideal.span {q}) := by
  refine IsField.toField ?_
  refine (Ideal.Quotient.maximal_ideal_iff_isField_quotient (Ideal.span {q})).1 ?_
  have _ : Fact (Irreducible q) := ⟨irr_q⟩
  exact AdjoinRoot.span_maximal_of_irreducible

def pb₁ : PowerBasis F (AdjoinRoot p) := AdjoinRoot.powerBasis' (g := p) (by monicity!)
def pb₂ : PowerBasis F (AdjoinRoot q) := AdjoinRoot.powerBasis' (g := q) (by monicity!)

instance finite₁ : Finite (F[X] ⧸ Ideal.span {p}) := by
  rw [← @Module.finite_iff_finite F]
  exact .of_basis pb₁.basis

instance finite₂ : Finite (F[X] ⧸ Ideal.span {q}) := by
  rw [← @Module.finite_iff_finite F]
  exact .of_basis pb₂.basis

instance fin₁ : Fintype (AdjoinRoot p) := by
  change Fintype (F[X] ⧸ Ideal.span {p})
  exact Fintype.ofFinite _

instance fin₂ : Fintype (AdjoinRoot q) := by
  change Fintype (F[X] ⧸ Ideal.span {q})
  exact Fintype.ofFinite _

def iso : (F[X] ⧸ Ideal.span {p}) ≃ₐ[F] (F[X] ⧸ Ideal.span {q}) := by
  refine @FiniteField.algEquivOfCardEq (F[X] ⧸ Ideal.span {p}) fie₁ (Fintype.ofFinite _)
    (F[X] ⧸ Ideal.span {q}) fie₂ (Fintype.ofFinite _) 7 _ _ _ ?_
  change Fintype.card (AdjoinRoot p) = Fintype.card (AdjoinRoot q)
  rw [Module.card_fintype pb₁.basis, Module.card_fintype pb₂.basis]
  congr 1
  simp only [Fintype.card_fin]
  dsimp [pb₁, pb₂]
  rw [p_natDegree, q_natDegree]

end

end Exercise_6245

namespace UnexploredExercise_338_1

/-域的二次扩张 $E / F$ 必是正规扩张-/

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  (hdim : Module.finrank F E = 2)

include hdim

lemma findim : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hdim

lemma alg : Algebra.IsAlgebraic F E :=
  let _ := findim hdim
  Algebra.IsAlgebraic.of_finite F E

open Polynomial in
/-- Any field extension of degree 2 is a normal extension. -/
lemma normal : Normal F E where
  -- Proof that every element x in E is algebraic over F.
  isAlgebraic :=
    let _ := alg hdim
    Algebra.IsAlgebraic.isAlgebraic
  -- Proof that the minimal polynomial of any x in E splits over E.
  splits' x := by
    -- Take an arbitrary element x in E.
    -- Use the algebraic property.
    let _ := alg hdim
    -- The degree of the minimal polynomial of x over F is at most the dimension of E/F.
    have le_two : (minpoly F x).natDegree ≤ 2 :=
      hdim ▸ @minpoly.natDegree_le F _ E _ _ x (findim hdim)
    -- Since x is algebraic, it is integral over F.
    have integral : IsIntegral F x :=
      isAlgebraic_iff_isIntegral.mp <| Algebra.IsAlgebraic.isAlgebraic x
    -- The minimal polynomial has positive degree because x is integral
    have ge_zero : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos integral
    -- Let c be the degree of the minimal polynomial.
    set c := (minpoly F x).natDegree with def_c
    -- Case analysis on the degree c (must be 1 or 2).
    match c with
    -- Case 1: Degree is 1.
    | 1 =>
      -- Polynomials of degree 1 always split.
      exact splits_of_natDegree_eq_one (algebraMap F E) def_c.symm
    -- Case 2: Degree is 2.
    | 2 =>
      -- Since x is a root of its minimal polynomial, $(X - C x)$ divides $minpoly \ F \ x$
      -- when mapped to $E[X]$.
      obtain ⟨f, hf⟩ : X - C x ∣ map (algebraMap F E) (minpoly F x) := by
        -- Use the definition of divisibility via roots.
        refine dvd_iff_isRoot.mpr ?_
        -- Show that x is a root of the mapped minimal polynomial.
        simp only [IsRoot.def, eval_map_algebraMap, minpoly.aeval]
      -- The other factor $f$ cannot be zero.
      have f_ne_zero : f ≠ 0 := by
        -- Assume $f = 0$.
        by_contra!
        -- Then map $(minpoly \ F \ x) = 0$.
        rw [this, mul_zero, Polynomial.map_eq_zero] at hf
        -- This implies $minpoly \ F \ x = 0$.
        rw [hf] at def_c
        -- But the degree is 2, not 0.
        contrapose! def_c
        simp only [natDegree_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      -- Calculate the degree of $f$.
      -- Take degrees of both sides of hf.
      have hf_deg := congrArg (·.natDegree) hf
      -- Degree is preserved by map.
      simp only [natDegree_map] at hf_deg
      -- Use natDegree_mul: $deg(minpoly) = deg(X - C x) + deg(f)$.
      rw [natDegree_mul (X_sub_C_ne_zero x) f_ne_zero, def_c.symm, natDegree_X_sub_C] at hf_deg
      -- Since $2 = 1 + deg(f)$, $deg(f)$ must be 1.
      replace hf_deg : f.natDegree = 1 := by omega
      -- To show $minpoly \ F \ x$ splits, we need every irreducible factor
      -- $m$ over F to have degree 1 over E.
      -- Use the definition of `Splits`.
      refine Or.intro_right _ ?_
      -- Let $m$ be an irreducible factor of $minpoly \ F \ x$ over F.
      rintro m hirr ⟨g, hm⟩
      -- The other factor $g$ cannot be zero.
      have g_ne_zero : g ≠ 0 := by
        -- Assume $g = 0$.
        by_contra!
        -- Then $map \ m = 0$.
        rw [this, mul_zero, Polynomial.map_eq_zero] at hm
        -- This implies $m = 0$.
        rw [hm] at def_c
        -- But $m$ is irreducible, so not zero, degree is not 0.
        contrapose! def_c
        simp only [natDegree_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      -- Calculate degrees relating m and g.
      have hm_deg := congrArg (·.natDegree) hm
      simp only [natDegree_map] at hm_deg
      -- Use natDegree_mul: $deg(minpoly) = deg(m) + deg(g)$.
      rw [def_c.symm, natDegree_mul (Irreducible.ne_zero hirr) g_ne_zero] at hm_deg
      -- So $2 = deg(m) + deg(g)$.
      -- Degree of $m$ is at most 2.
      have le : m.natDegree ≤ 2 := by omega
      -- Let d be the degree of $m$.
      set d := m.natDegree with def_d
      -- Case analysis on the degree d of the irreducible factor $m$ (must be 0, 1, or 2).
      match d with
      -- Case d = 0: $m$ is a constant.
      | 0 =>
        -- If natDegree is 0, the polynomial is a non-zero constant.
        obtain ⟨l, hl⟩ := natDegree_eq_zero.1 def_d.symm
        -- Substitute $m = C l$ into irreducibility.
        rw [← hl] at hirr
        -- Constants are not irreducible.
        exact False.elim <| (not_irreducible_C l) hirr
      -- Case d = 1: $m$ has degree 1.
      | 1 =>
        show m.degree = (1 : ℕ) -- Goal is to show degree is 1.
        rw [degree_eq_iff_natDegree_eq (Irreducible.ne_zero hirr), def_d] -- This case satisfies the goal.
      -- Case d = 2: m has degree 2.
      | 2 =>
        -- From $2 = deg(m) + deg(g)$, we get $2 = 2 + deg(g)$, so $deg(g) = 0$.
        rw [self_eq_add_right] at hm_deg
        -- If natDegree is 0, g is a non-zero constant $C l$.
        obtain ⟨l, hl⟩ := natDegree_eq_zero.1 hm_deg
        rw [← hl] at hm -- Substitute $g = C l$ into $hm$.
        -- $map (minpoly) = map \ m * C l$. So $map \ m$ and $map \ minpoly$ are associated.
        have min_monic : (map (algebraMap F E) (minpoly F x)).Monic :=
          -- Mapped minpoly is monic.
          Monic.map (algebraMap F E) <| minpoly.monic integral
        -- Since $map \ m * C l$ is monic, $C l$ must be 1 (as map m is also monic implicitly).
        have l_dvd : C l ∣ map (algebraMap F E) (minpoly F x) := ⟨m, by rwa [mul_comm] at hm⟩
        -- $C l$ must be a unit. Since monic, $l=1$.
        obtain ⟨b, hb⟩ := isUnit_iff_exists.1 <| (Monic.C_dvd_iff_isUnit min_monic).1 l_dvd
        -- Substitute $map (minpoly) = (X - C x) * f$ into hm.
        rw [hf] at hm -- $(X - C x) * f = map \ m * C l$
        -- Multiply by $(C l)^{-1} = C b$.
        apply_fun (· * C b) at hm
        -- $(X - C x) * f * C b = map \ m$
        rw [mul_assoc, mul_assoc, ← C_mul, hb.1, C_1, mul_one] at hm
        -- Now $map \ m = (X - C x) * (f * C b)$.
        -- If $map \ m$ were irreducible over E, then one factor must be a unit.
        have := hirr.2 (X - C x) (f * C b) hm.symm
        -- Check if $X - C x$ is a unit. It's not.
        have not_unit₁ : ¬ IsUnit (X - C x) := not_isUnit_X_sub_C x
        -- Check if $f * C b$ is a unit.
        have not_unit₂ : ¬ IsUnit (f * C b) := by
          -- Assume it is a unit.
          by_contra! h_unit
          -- Units have degree 0.
          have := natDegree_eq_zero_of_isUnit h_unit
          -- $f * C b$ is non-zero because it's a unit.
          have fb_ne_zero : f * C b ≠ 0 := IsUnit.ne_zero h_unit
          -- Look at degrees in $map \ m = (X - C x) * (f * C b)$.
          have hm_deg := congrArg (·.natDegree) hm
          simp only at hm_deg
          -- $deg(map \ m) = deg(X - C x) + deg(f * C b)$
          -- $2 = 1 + 0 = 1$. Contradiction.
          rw [natDegree_mul (X_sub_C_ne_zero x) fb_ne_zero, def_d.symm,
            natDegree_X_sub_C, this, add_zero] at hm_deg
          trivial
        -- Assume $map \ m$ is irreducible.
        contrapose! this
        -- Then both factors must not be units. This doesn't contradict anything yet.
        exact ⟨not_unit₁, not_unit₂⟩


end UnexploredExercise_338_1
