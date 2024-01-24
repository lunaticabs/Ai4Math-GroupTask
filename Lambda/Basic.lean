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

@[simp]
def subst : Term -> Sym -> Term -> Term
  | ` x, y, t => if x = y then t else ` x

  | λ x : t, y, z =>
    if x = y then λ x : t else λ x : (subst t y z)

  | App x y , z, t =>
    subst x z t $ subst y z t

notation : 90 x " [ " y " := " v " ] " => subst x y v

def commute : ∀ (M N L : Term) (x y : Sym) (h : x ≠ y),
  M [x := N] [y := L] = M [y := L] [x := N [y := L]] := by
    intro M N L x y h
    induction M with
    | Var M =>
      simp
      by_cases g : M = x

      -- when M = x
      rw [ g ]
      simp
      rw [ if_neg ]
      simp
      exact h

      -- when M ≠ x
      by_cases i : M = y

      -- when M ≠ x and M = y
      rw [ if_neg, if_pos ]
      simp
      rw [ if_pos ]
      induction N with
      | Var N =>
        simp
        by_cases j : N = y

        -- when N = y
        rw [ if_pos ]
        -- here's sorry is because x is not in FV(L),
        -- but this is hard to formal now.
        sorry
        exact j

        -- when N ≠ y
        rw [ if_neg ]
        -- sorry because of the same reason.
        sorry
        exact j

      | Lam _ _ => sorry
      | App _ _ => sorry
      repeat exact i
      exact g

      -- when M ≠ x and M ≠ y
      rw [ if_neg, if_neg ]
      simp
      rw [ if_neg, if_neg ]
      exact g
      repeat exact i
      exact g


    | Lam _ _ => sorry
    | App _ _ => sorry

inductive Reduce : Term -> Term -> Type where
  | Reduce : Reduce (App (Lam x t) y) (t[x := y])

notation : 50 M " ~> " N => Reduce M N

def compatibility_r : (M ~> N) -> ((App M L) ~> (App N L)) := sorry
def compatibility_l : (M ~> N) -> ((App L M) ~> (App L N)) := sorry
def compatibility : (M ~> N) -> ((Lam x M) ~> (Lam x N)) := sorry

def β_redu : Term → Term :=
  sorry


variable (m : Sym )(n p q: Term)

#check if_neg
