def Sym : Type := String deriving BEq, DecidableEq, Repr


inductive Term where
| Var : Sym → Term
| Lam : Sym → Term → Term
| App : Term → Term → Term
deriving Repr


namespace Term
notation : 50 "λ " v " : " d => Lam v d
infixr : min " $ " => App
prefix : 90 "` " => Var


def subst : Term -> Sym -> Term -> Term
  | ` x, y, t => if x == y then t else ` x

  | λ x : t, y, z =>
    if x == y then λ x : t else λ x : (subst t y z)

  | App x y , z, t =>
    subst x z t $ subst y z t

notation : 90 x " [ " y " := " v " ] " => subst x y v

def commute : ∀ M N x y,
  M [x := N] [y := L] = M [y := L] [x := N] :=
    fun M N x y =>
      match M with
      | ` M => sorry
        -- if M == x then (` M) [y := L][x := N] = (` M) [x := N] [y := L]
        -- else L = M[y := L][x := N]
      | (λ α : β) => sorry
      | App α β => sorry

inductive Reduce : Term -> Term -> Type where
  | Reduce : Reduce (App (Lam x t) y) (t[x := y])

notation : 50 M " ~> " N => Reduce M N

def compatibility_r : (M ~> N) -> ((App M L) ~> (App N L)) := sorry
def compatibility_l : (M ~> N) -> ((App L M) ~> (App L N)) := sorry
def compatibility : (M ~> N) -> ((Lam x M) ~> (Lam x N)) := sorry

def β_redu : Term → Term :=
  sorry


variable (m : Sym )(n p q: Term)
