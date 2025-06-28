import Dpda.Basic
import Dpda.WobblyFn
import Dpda.PushOrPop1
import Dpda.PushOrPop2

universe u_

abbrev PADWTC (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  AugmentZ0 Γ → Option (Q ⊕ (S → Option Q))

def embedPADWTC {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (f: PADWTC Q S Γ) : AugmentZ0 Γ → Option (WobblyFn S Q)
  :=
  fun Γz => match f Γz with
  | none => none
  | some u => WobblyFn.from u

inductive PTPP_Judge (Q: Type u_) (S: Type u_) (Γ: Type u_)
  | uncondPush : (Γ × Q) → PTPP_Judge Q S Γ
  | popAndDecideWhetherToConsume : PADWTC Q S Γ → PTPP_Judge Q S Γ

abbrev PTPP_Transition (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  Q → PTPP_Judge Q S Γ

structure PTPP_DPDA_IDesc (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  p : Q
  w : List S
  β : List Γ

structure PTPP_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  q0 : Q
  F : Finset Q
  transition : PTPP_Transition Q S Γ

def PTPP_DPDA.embedInPP2 {Q: Type u_} {S: Type u_} {Γ: Type u_} (M: PTPP_DPDA Q S Γ)
  : PP2_DPDA Q S Γ :=
  { q0 := M.q0
  , F := M.F
  , transition := fun q =>
      match M.transition q with
      | PTPP_Judge.popAndDecideWhetherToConsume f =>
        PP2_Judge.uncondPop fun Γz =>
          (embedPADWTC f Γz : Option (WobblyFn S Q)).map
          (WobblyFn.fmap fun q => ((), q))
      | PTPP_Judge.uncondPush γq =>
        PP2_Judge.observeInput (WobblyFn.noWant (.inl γq))
  }

def PTPP_DPDA.embedInPP1 {Q: Type u_} {S: Type u_} {Γ: Type u_} (M: PTPP_DPDA Q S Γ)
  : PP1_DPDA Q S Γ :=
  { q0 := M.q0
  , F := M.F
  , transition := fun q =>
      match M.transition q with
      | PTPP_Judge.popAndDecideWhetherToConsume f =>
        PP1_Judge.popAndDecideWhetherToConsume f
      | PTPP_Judge.uncondPush γq =>
        PP1_Judge.unconditionalPush γq
  }

def PTPP_DPDA.embed_commutes {Q: Type u_} {S: Type u_} {Γ: Type u_}
  : ∀ (M: PTPP_DPDA Q S Γ),
    M.embedInPP1.embedInPP2 = M.embedInPP2 := by
    intro M
    obtain ⟨ q0, F, transition ⟩ := M
    unfold PTPP_DPDA.embedInPP1
    unfold PTPP_DPDA.embedInPP2
    unfold PP1_DPDA.embedInPP2
    simp only [PP2_DPDA.mk.injEq, true_and]
    ext q
    cases transition q with
    | uncondPush f =>
      rfl
    | popAndDecideWhetherToConsume a2 =>
      cases PTPP_Judge.popAndDecideWhetherToConsume a2 with
      | uncondPush g => rfl
      | popAndDecideWhetherToConsume g =>
        simp only [PP2_Judge.uncondPop.injEq]
        unfold inclusionUnit
        ext Γz a
        unfold embedPADWTC
        match g Γz with
        | none => simp
        | some (.inr f) =>
          simp only [Option.some.injEq, Option.map_some, WobblyFn.fmap]
          match a with
          | WobblyFn.noWant v =>
            have h := WobblyFn.want_ne_nowant (fun s ↦
                match f s with
                | none => none
                | some q => some ((), q)) v
            simp only [reduceCtorEq, WobblyFn.from]
          | WobblyFn.want f' =>
            simp only [WobblyFn.want.injEq, WobblyFn.from]
            rfl
        | some (.inl q) =>
          simp only [Option.some.injEq, WobblyFn.from, Option.map_some, WobblyFn.fmap]
