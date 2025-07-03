import Dpda.Definition.PredeterminedToPushOrPop
import Dpda.Definition.PushOrPop1
import Dpda.Definition.PushOrPop2
import Dpda.Conversion.PP1ToPP2

universe u_

def embedPADWTC {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (f: PADWTC Q S Γ) : AugmentZ0 Γ → Option (WobblyFn S Q)
  :=
  fun Γz => match f Γz with
  | none => none
  | some u => WobblyFn.from u

def Predet_DPDA.embedInPP2 {Q: Type u_} {S: Type u_} {Γ: Type u_} (M: Predet_DPDA Q S Γ)
  : PP2_DPDA Q S Γ :=
  { q0 := M.q0
  , F := M.F
  , transition := fun q =>
      match M.transition q with
      | Predet_Judge.popAndDecideWhetherToConsume f =>
        PP2_Judge.uncondPop fun Γz =>
          (embedPADWTC f Γz : Option (WobblyFn S Q)).map
          (WobblyFn.fmap fun q => ((), q))
      | Predet_Judge.uncondPush γq =>
        PP2_Judge.observeInput (WobblyFn.noWant (.inl γq))
  }

def Predet_DPDA.embedInPP1 {Q: Type u_} {S: Type u_} {Γ: Type u_} (M: Predet_DPDA Q S Γ)
  : PP1_DPDA Q S Γ :=
  { q0 := M.q0
  , F := M.F
  , transition := fun q =>
      match M.transition q with
      | Predet_Judge.popAndDecideWhetherToConsume f =>
        PP1_Judge.popAndDecideWhetherToConsume f
      | Predet_Judge.uncondPush γq =>
        PP1_Judge.unconditionalPush γq
  }

def Predet_DPDA.embed_commutes {Q: Type u_} {S: Type u_} {Γ: Type u_}
  : ∀ (M: Predet_DPDA Q S Γ),
    M.embedInPP1.embedInPP2 = M.embedInPP2 := by
    intro M
    obtain ⟨ q0, F, transition ⟩ := M
    unfold Predet_DPDA.embedInPP1
    unfold Predet_DPDA.embedInPP2
    unfold PP1_DPDA.embedInPP2
    simp only [PP2_DPDA.mk.injEq, true_and]
    ext q
    cases transition q with
    | uncondPush f =>
      rfl
    | popAndDecideWhetherToConsume a2 =>
      cases Predet_Judge.popAndDecideWhetherToConsume a2 with
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
