import Lean

open Lean Elab Command Term Meta

def Iden : Type := String deriving BEq, DecidableEq, Repr

inductive LTerm where
  | 𝕍 : Iden → LTerm
  | Appl : LTerm → LTerm → LTerm
  | 𝕃 : LTerm → LTerm → LTerm

-- usage: bindingVariable → objectTerm → result
def Abstract : LTerm → LTerm → LTerm :=
  fun bd tm =>
    .𝕃 bd tm

def Apply : LTerm → LTerm → LTerm :=
  fun m n =>
    .Appl m n

infixl:40 " =α " =>
  fun l r => rfl l r

def β_redu : LTerm → LTerm :=
  fun m =>
    match m with
    | .Appl (.𝕃 q n) p => if (q == n) then p else n
    | _ => m
