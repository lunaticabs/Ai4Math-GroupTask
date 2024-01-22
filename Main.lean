import «FSystem»


-- 定义 Type
inductive Kind : Type
  | empty : Kind --空类型
  | unit : Kind  --单位类型
  | function : Kind → Kind → Kind   --函数类型


-- 定义 Ctx , i.e. Γ ctx, A kind --> {Γ, x : A} ctx, where we replace two variables with double type
inductive Ctx : Type
  | empty : Ctx                           -- 空语境
  | extend : Ctx → Kind → Ctx             -- 语境扩展


inductive Var : Ctx → Kind → Type --Var规则
| Z {Φ J} : Var (Ctx.extend Φ J) J
| S {Φ J K} : Var Φ J → Var (Ctx.extend Φ K) J

inductvie

-- Term 类型的定义，包含单位类型的元素和变量引入规则
inductive Term : Ctx → Kind → Type
| unitElem {Γ : Ctx} : Term Γ Kind.unit
| varElem {Γ : Ctx} {J : Kind} : Var Γ J → Term Γ J
| introduceVar {Γ : Ctx} {A : Kind} : Term Γ A → Term (Ctx.extend Γ A) A
