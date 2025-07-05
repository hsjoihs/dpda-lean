import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Dpda.AugmentSingleton

structure Sipser_PreDPDA (Q S Γ) where
  q0 : Q
  F : Finset Q
  transition : Q × AugmentEpsilon S × AugmentEpsilon Γ -> Option (Q × AugmentEpsilon Γ)

def exactly_one_some {α}
  (o1 : Option α)
  (o2 : Option α)
  (o3 : Option α)
  (o4 : Option α) := match o1, o2, o3, o4 with
  | some _, none, none, none => true
  | none, some _, none, none => true
  | none, none, some _, none => true
  | none, none, none, some _ => true
  | _, _, _, _ => false

structure Sipser_DPDA(Q S Γ) where
  pda : Sipser_PreDPDA Q S Γ
  deterministic : ∀ q a x,
    exactly_one_some
      (pda.transition (q, AugmentEpsilon.fromChar a, AugmentEpsilon.fromChar x))
      (pda.transition (q, AugmentEpsilon.fromChar a, AugmentEpsilon.Epsilon))
      (pda.transition (q, AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar x))
      (pda.transition (q, AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon))

structure Sipser_DPDA_IDesc (Q) (S) (Γ) where
  p : Q
  w : List S
  β : List Γ


-- This is the version that does not depend on the `deterministic` condition.
-- This is intended as a workaround in Lean's `motive is not type correct` error.
def Sipser_PreDPDA.stepTransition {Q S Γ}
  (M: Sipser_PreDPDA Q S Γ)
  (pwβ: Sipser_DPDA_IDesc Q S Γ)
  : Option (Sipser_DPDA_IDesc Q S Γ) :=
  /-

  A Sipser DPDA has exactly one legal move in every situation where its stack is nonempty.
  If the stack is empty, a Sipser DPDA can move only if the transition function specifies a move that pops ε.
  -/

  match M.transition (pwβ.p, AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon) with
  | some (r, y) =>
    -- If δ(q, ε, ε) is nonempty, there is no restriction on the input or stack.
    -- · move to the state r,
    -- · consume nothing from the input
    -- · pop nothing from the stack
    -- · push y onto the stack
    some ⟨ r, pwβ.w, y.toList ++ pwβ.β ⟩
  | none =>
    -- Otherwise, ∀ a x, exactly one of δ(q, a, x), δ(q, ε, x), or δ(q, a, ε) is `some`.
    -- Thus we first need to check whether the stack or the input is empty.
    match pwβ.w, pwβ.β with
    | [], [] =>
      -- If both the input and the stack are empty, we cannot move,
      -- since the only potential legal move, δ(q, ε, ε), turned out to be empty.
      none
    | [], x :: xs =>
      -- We cannot consume from an empty input, so our only hope is δ(q, ε, x), a transition without the input consumption.
      match M.transition (pwβ.p, AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar x) with
      | some (r, y) =>
        -- If δ(q, ε, x) is nonempty, we can pop x from the stack,
        -- move to the state r,
        -- consume nothing from the input,
        -- and push y onto the stack.
        some ⟨ r, pwβ.w, y.toList ++ xs ⟩
      | none =>
        -- If δ(q, ε, x) is empty, we cannot move.
        none
    | a :: ws, [] =>
      -- If the stack is empty, our only legal option is δ(q, a, ε), a transition without the stack pop.
      match M.transition (pwβ.p, AugmentEpsilon.fromChar a, AugmentEpsilon.Epsilon) with
      | some (r, y) =>
        -- If δ(q, a, ε) is nonempty, we can consume a from the input,
        -- move to the state r,
        -- pop nothing from the stack,
        -- and push y onto the stack.
        some ⟨ r, ws, y.toList ++ pwβ.β ⟩
      | none =>
        -- If δ(q, a, ε) is empty, we cannot move.
        none
    | a :: ws, x :: xs =>
      -- If both the input and the stack are nonempty, we have options.
      -- Exactly one of δ(q, a, x), δ(q, ε, x), or δ(q, a, ε) is `some`, and we have to choose the one that is `some`.
      match
        (M.transition (pwβ.p, AugmentEpsilon.fromChar a, AugmentEpsilon.fromChar x)),
        (M.transition (pwβ.p, AugmentEpsilon.fromChar a, AugmentEpsilon.Epsilon)),
        (M.transition (pwβ.p, AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar x)) with
      | some (r, y), none, none =>
        -- If δ(q, a, x) is nonempty, we can consume a from the input,
        -- move to the state r,
        -- pop x from the stack,
        -- and push y onto the stack.
        some ⟨ r, ws, y.toList ++ xs ⟩
      | none, some (r, y), none =>
        -- If δ(q, ε, x) is nonempty, we can pop x from the stack,
        -- move to the state r,
        -- consume nothing from the input,
        -- and push y onto the stack.
        some ⟨ r, pwβ.w, y.toList ++ xs ⟩
      | none, none, some (r, y) =>
        -- If δ(q, a, ε) is nonempty, we can consume a from the input,
        -- move to the state r,
        -- pop nothing from the stack,
        -- and push y onto the stack.
        some ⟨ r, ws, y.toList ++ pwβ.β ⟩
      | _, _, _ => none -- When the `deterministic` condition holds, this branch should never be reached.


def Sipser_DPDA.stepTransition {Q S Γ}
  (M: Sipser_DPDA Q S Γ)
  (pwβ: Sipser_DPDA_IDesc Q S Γ)
  : Option (Sipser_DPDA_IDesc Q S Γ) :=
  /-

  A Sipser DPDA has exactly one legal move in every situation where its stack is nonempty.
  If the stack is empty, a Sipser DPDA can move only if the transition function specifies a move that pops ε.
  -/

  match hεε : M.pda.transition (pwβ.p, AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon) with
  | some (r, y) =>
    -- If δ(q, ε, ε) is nonempty, there is no restriction on the input or stack.
    -- · move to the state r,
    -- · consume nothing from the input
    -- · pop nothing from the stack
    -- · push y onto the stack
    some ⟨ r, pwβ.w, y.toList ++ pwβ.β ⟩
  | none =>
    -- Otherwise, ∀ a x, exactly one of δ(q, a, x), δ(q, ε, x), or δ(q, a, ε) is `some`.
    -- Thus we first need to check whether the stack or the input is empty.
    match pwβ.w, pwβ.β with
    | [], [] =>
      -- If both the input and the stack are empty, we cannot move,
      -- since the only potential legal move, δ(q, ε, ε), turned out to be empty.
      none
    | [], x :: xs =>
      -- We cannot consume from an empty input, so our only hope is δ(q, ε, x), a transition without the input consumption.
      match h2 : M.pda.transition (pwβ.p, AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar x) with
      | some (r, y) =>
        -- If δ(q, ε, x) is nonempty, we can pop x from the stack,
        -- move to the state r,
        -- consume nothing from the input,
        -- and push y onto the stack.
        some ⟨ r, pwβ.w, y.toList ++ xs ⟩
      | none =>
        -- If δ(q, ε, x) is empty, we cannot move.
        none
    | a :: ws, [] =>
      -- If the stack is empty, our only legal option is δ(q, a, ε), a transition without the stack pop.
      match h2 : M.pda.transition (pwβ.p, AugmentEpsilon.fromChar a, AugmentEpsilon.Epsilon) with
      | some (r, y) =>
        -- If δ(q, a, ε) is nonempty, we can consume a from the input,
        -- move to the state r,
        -- pop nothing from the stack,
        -- and push y onto the stack.
        some ⟨ r, ws, y.toList ++ pwβ.β ⟩
      | none =>
        -- If δ(q, a, ε) is empty, we cannot move.
        none
    | a :: ws, x :: xs =>
      -- If both the input and the stack are nonempty, we have options.
      -- Exactly one of δ(q, a, x), δ(q, ε, x), or δ(q, a, ε) is `some`, and we have to choose the one that is `some`.
      match
        hax : (M.pda.transition (pwβ.p, AugmentEpsilon.fromChar a, AugmentEpsilon.fromChar x)),
        haε : (M.pda.transition (pwβ.p, AugmentEpsilon.fromChar a, AugmentEpsilon.Epsilon)),
        hεx : (M.pda.transition (pwβ.p, AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar x)) with
      | some (r, y), none, none =>
        -- If δ(q, a, x) is nonempty, we can consume a from the input,
        -- move to the state r,
        -- pop x from the stack,
        -- and push y onto the stack.
        some ⟨ r, ws, y.toList ++ xs ⟩
      | none, some (r, y), none =>
        -- If δ(q, ε, x) is nonempty, we can pop x from the stack,
        -- move to the state r,
        -- consume nothing from the input,
        -- and push y onto the stack.
        some ⟨ r, pwβ.w, y.toList ++ xs ⟩
      | none, none, some (r, y) =>
        -- If δ(q, a, ε) is nonempty, we can consume a from the input,
        -- move to the state r,
        -- pop nothing from the stack,
        -- and push y onto the stack.
        some ⟨ r, ws, y.toList ++ pwβ.β ⟩
      | some _, some _, some _ => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | some _, some _, none   => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | some _, none, some _   => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | none, some _, some _   => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | none, none, none       => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
