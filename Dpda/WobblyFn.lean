import Dpda.Basic

inductive WobblyFn U V
  | want : (U → Option V) → WobblyFn U V
  | noWant : V → WobblyFn U V

-- wobbly consumption
def wob {U V} (wf : WobblyFn U V) (s : List U) : Option (V × List U) :=
  match wf with
  | WobblyFn.noWant v => some (v, s)
  | WobblyFn.want f => match s with
    | [] => none
    | A :: t =>
      match f A with
      | none => none
      | some v => some (v, t)

-- wobbly consumption, with the semantics that an empty stack always produces a Z0 when popped
def wobZ {Γ V} (wf : WobblyFn (AugmentZ0 Γ) V) (β : List Γ) : Option (V × List Γ) :=
  match wf with
  | WobblyFn.noWant v => some (v, β)
  | WobblyFn.want f => match β with
    | [] =>  match f AugmentZ0.z0 with
      | none => none
      | some v => some (v, [])
    | A :: γ =>
      match f (AugmentZ0.fromΓ A) with
      | none => none
      | some v => some (v, γ)

universe u_

def WobblyFn.fmap {S: Type u_} {U: Type u_} {V: Type u_} (η: U → V) (wf: WobblyFn S U) : WobblyFn S V :=
  match wf with
  | .noWant u => WobblyFn.noWant (η u)
  | .want f => WobblyFn.want fun s =>
    match f s with
    | none => none
    | some u => some (η u)
