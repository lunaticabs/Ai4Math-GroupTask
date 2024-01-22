import «FSystem»

--这是一个最简单的STLC版本，由于STLC只有一个单位类型元素唯一，我们在这里可以使用类型来代替具体的项
--因此在定义中规约关系几乎被商掉了
--但是他几乎不可拓展，只能作为一个最初版本
--加上别的类型后，我们可以在里面谈论命题逻辑

-- 定义 Type
inductive Kind : Type
  | empty : Kind --空类型
  | unit : Kind  --单位类型
  | function : Kind → Kind → Kind   --函数类型
  | unknown : String → Kind   --未知类型，我们不会谈论他包含的任何常量

-- 定义 Ctx , i.e. Γ ctx, A kind --> {Γ, x : A} ctx, where we replace two variables with double type
inductive Ctx : Type
  | empty : Ctx                           -- 空语境
  | extend : Ctx → Kind → Ctx             -- 语境扩展


inductive Var : Ctx → Kind → Type --Var规则
  | Z {Γ J} : Var (Ctx.extend Γ J) J
  | S {Γ J K} : Var Γ J → Var (Ctx.extend Γ K) J

inductive Lam : Ctx → Kind → Type --Lam规则
  | Z {Γ J K} : Lam (Ctx.extend Γ J) K → Lam Γ (Kind.function J K)
  | S {Γ J K} : Lam Γ J → Lam (Ctx.extend Γ K) J


-- 语法树的组成元素Term,i.e.{Γ|-J} where x:J 是内蕴的，因为STLC
inductive Term : Ctx → Kind → Type
  | unitElem {Γ : Ctx} : Term Γ Kind.unit
  | unknownElem {str : String } {Γ : Ctx} :Term Γ (Kind.unknown str)
  | varElem {Γ : Ctx} {J : Kind} : Var Γ J → Term Γ J
  | LamElem {Γ : Ctx} {A : Kind} : Lam Γ J → Term Γ J

--这个版本太烂了，我要写个新的
