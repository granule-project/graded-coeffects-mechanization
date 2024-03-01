
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module GrCore where

open import Data.Product
open import Data.Sum
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-comm)
open import Data.Nat hiding (_≟_; _≤_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Maybe
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤_)
open import Data.Fin using (Fin; _≟_; raise; fromℕ; inject; inject!; compare)

open import Semiring

open Semiring.Semiring {{...}} public

variable
  s : ℕ

-- # Types of GrCore

data Type {{R : Semiring}} : Set where
  FunTy : (A : Type) -> (r : grade) -> (B : Type) -> Type -- A r -> B
  Unit  : Type
  Box   : (r : grade) -> Type -> Type
  --------------------------------------------------
  -- Prod  : Type -> Type -> Type
  -- Sum   : Type -> Type -> Type
  BoolTy : Type

-- # Contexts for GrCore

data Assumption {{R : Semiring}} : Set where
--  Lin : (A : Type)                    -> Assumption A
  Grad : (A : Type) -> (r : grade) -> Assumption

-- position 0 is Grad r A
-- position 1 is Grade s B
-- Ext (Ext Empty (Grad s B)) (Grad r A)
-- . , x :_s B , y :_r A

data Context {{R : Semiring}} : ℕ -> Set where
  Empty   : Context 0
  Ext     : {s : ℕ} -> Context s -> Assumption -> Context (1 + s)

-- # Some properties of contexts

injGradTy : {{R : Semiring}} {A A' : Type} {r r' : grade} -> Grad A r ≡ Grad A' r' -> A ≡ A'
injGradTy refl = refl

injGradR : {{R : Semiring}} {A A' : Type} {r r' : grade} -> Grad A r ≡ Grad A' r' -> r ≡ r'
injGradR refl = refl

injExt1 : {{R : Semiring}} {s : ℕ} {Γ Γ' : Context s} {A A' : Assumption} -> Ext Γ A ≡ Ext Γ' A' -> Γ ≡ Γ'
injExt1 refl = refl

injExt2 : {{R : Semiring}} {s : ℕ} {Γ Γ' : Context s} {A A' : Assumption} -> Ext Γ A ≡ Ext Γ' A' -> A ≡ A'
injExt2 refl = refl

-- # Context operations

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

{-# REWRITE +-identityʳ +-suc #-}

-- Disjoint context concatentation
_,,_ : {{R : Semiring}} {s t : ℕ} -> Context s -> Context t -> Context (s + t)
G1 ,, Empty = G1
G1 ,, (Ext G2 a) = Ext (G1 ,, G2) a

-- Context scalar multiplication
_·_ : {{R : Semiring}} {s : ℕ} -> grade -> Context s -> Context s
r · Empty = Empty
r · Ext g (Grad A s) = Ext (r · g) (Grad A (r *R s))

-- Context addition
_++_ : {{R : Semiring}} {s : ℕ} -> Context s -> Context s -> Context s
Empty ++ Empty = Empty
(Ext G (Grad A r)) ++ (Ext G' (Grad B s)) = Ext (G ++ G') (Grad A (r +R s))

-- Context scalar multiplication distributes with context contactentation
multConcatDistr : {{R : Semiring}} {s t : ℕ} {r : grade} {Γ1 : Context s} {Γ2 : Context t} ->
                  r · (Γ1 ,, Γ2) ≡ ((r · Γ1) ,, (r · Γ2))
multConcatDistr ⦃ R ⦄ {.0} {t} {r} {Empty} {Γ2} = {!!}
multConcatDistr ⦃ R ⦄ {suc n} {t} {r} {Ext Γ1 (Grad A s)} {Γ2}
  rewrite multConcatDistr {n} {t} {r} {Γ1} {Γ2} = {!!}

postulate -- TODO: Vilem prove these
  -- keeps things simple with the above definition
  sameTypes : {{R : Semiring}} {s : ℕ} {Γ1 Γ2 : Context s} {Γ : Context (suc s)} {A A' : Type} {r1 r2 : grade}
            -> (Ext Γ1 (Grad A r1)) ++ (Ext Γ2 (Grad A' r2)) ≡ Γ -> A ≡ A'

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

absorptionContext : {{R : Semiring}} {s : ℕ} {Γ Γ' : Context s} -> (0R · Γ) ++ Γ' ≡ Γ'
absorptionContext {s = _} {Empty} {Empty}
  = refl
absorptionContext {s = _} {Ext Γ (Grad A1 r1)} {Ext Γ' (Grad A2 r2)} rewrite absorptionContext {_} {Γ} {Γ'}
  = let
      e : {r1 r2 : grade} → (0R *R r1) +R r2 ≡ r2
      e {r1} {r2} =
          (0R *R r1) +R r2
        ≡⟨ cong (_+R r2) leftAbsorb ⟩
          0R +R r2
        ≡⟨ leftUnit+ ⟩
          r2
        ∎
    in -- need to use sameTypes
      {!   !} -- cong (\r → Ext Γ' (Grad _ r)) e

--   Ext Γ' (Grad A1 ((R Semiring.+R (R Semiring.*R Semiring.0R R) r1) r2))
-- ≡ Ext Γ' (Grad A2 r2)


leftUnitContext : {{R : Semiring}} {s : ℕ} {Γ : Context s} -> 1R · Γ ≡ Γ
leftUnitContext {_} {Empty} = refl
leftUnitContext {suc s} {Γ = Ext G (Grad A r)} rewrite leftUnitContext {s} {G} =
  cong (λ r → Ext G (Grad A r)) leftUnit*

Γlength : {{R : Semiring}} {s : ℕ} -> Context s -> ℕ
Γlength Empty = 0
Γlength (Ext g a) = 1 + Γlength g

-- # Term calculus

data Term : ℕ -> Set where
  Var     : {s : ℕ} -> Fin (suc s) -> Term (suc s)
  App     : {s : ℕ} -> Term s -> Term s -> Term s
  Abs     : {s : ℕ} -> Term (suc s) -> Term s
  unit    : {s : ℕ} -> Term s
  Promote : {s : ℕ} -> Term s -> Term s
  Let     : {s : ℕ} -> Term s -> Term (suc s) -> Term s
  -- handling bools (TODO: generalise to sums)
  vtrue   : {s : ℕ} -> Term s
  vfalse  : {s : ℕ} -> Term s
  If      : {s : ℕ} -> Term s -> Term s -> Term s -> Term s

raiseTerm : {s : ℕ} -> Term s -> Term (suc s)
raiseTerm (Var x) = Var (raise 1 x)
raiseTerm (App t t₁) = App (raiseTerm t) (raiseTerm t₁)
raiseTerm (Abs t) = Abs (raiseTerm t)
raiseTerm unit = unit
raiseTerm (Promote t) = Promote (raiseTerm t)
raiseTerm vtrue = vtrue
raiseTerm vfalse = vfalse
raiseTerm (If t t₁ t₂) = If (raiseTerm t) (raiseTerm t₁) (raiseTerm t₂)
raiseTerm (Let t1 t2) = Let (raiseTerm t1) (raiseTerm t2)

raiseTermℕ : (n : ℕ) -> Term s -> Term (n + s)
raiseTermℕ = {!!}

-- `mathcVar` is used to enact substitution into a variable term
-- i.e., the situation is that we have a receiver:

--  G2, x : A, G3 |- y : B

-- and a substitutee

--  G1 |- t : A

-- where |G1| = |G2| + |G3|

-- The question is whether
--   (1) y = x and so we do substitution
--   (2) y is in G2 so we do not substitute but instead return pred of y position
--   (3) y is in G3 so we do not substitute but instead return just y

-- `matchVar x y t` computes the above

-- Uses the following helper:
-- `pred!` subtract 1 from an element of a finite set (shrinking its bound)
pred! : Fin (suc (suc s)) -> Fin (suc s)
pred! Fin.zero = Fin.zero
pred! (Fin.suc x) = x

matchVar : {s : ℕ} -> (t : Term s) ->  Fin (suc s) -> Fin (suc s) -> Term s
-- case (1) because we have singleton contexts
matchVar {zero} t Fin.zero Fin.zero = t

matchVar {suc s} t posx posy with Data.Fin.compare posy posx
-- case (1)
... | Data.Fin.equal .posx         = t

-- case (2)
... | Data.Fin.greater .posy least = Var (pred! posy)

-- case (3)
-- posx : Fin (suc (suc s))            | [[posx]]  = ix s.t., 0 <= ix < 2+s
-- posy : Fin (suc (suc s))            | [[posy]]  = iy s.t., 0 <= iy < 2+s
-- least : Fin' posx = Fin (toN posx)  | [[least]] = jy s.t., 0 <= jy < ix
... | Data.Fin.less .posx least    = Var (inject! least)

-- # Substitution

-- `syntacticSubst {s} t x_pos t'` represents the situation:

-- G1             |- t       : A  -- substitutee
-- G2, x : A, G3  |- t'      : B  -- receiver
-- G1 + (G2,G3)   |- [t/x]t' : B

-- where |G1| = |G2|+|G3| = s

syntacticSubst : {s : ℕ} -> (t : Term s) -> Fin (suc s) -> (t' : Term (suc s)) -> Term s
syntacticSubst t x (Var y) = matchVar t x y
syntacticSubst t x (App t1 t2) = App (syntacticSubst t x t1) (syntacticSubst t x t2)
syntacticSubst  t x (Abs t1) =
  Abs (syntacticSubst (raiseTerm t) (raise 1 x) t1)
syntacticSubst t x (Promote t1) = Promote (syntacticSubst t x t1)
syntacticSubst t x unit = unit
syntacticSubst t x vtrue = vtrue
syntacticSubst t x vfalse = vfalse
syntacticSubst t x (If t1 t2 t3) = If (syntacticSubst t x t1) (syntacticSubst t x t2) (syntacticSubst t x t3)
syntacticSubst t x (Let t1 t2) = Let (syntacticSubst t x t1) (syntacticSubst (raiseTerm t) (raise 1 x) t2)

discrimBool : {s : ℕ} -> vtrue {s} ≡ vfalse {s} -> ⊥
discrimBool ()

absInj2 : {s : ℕ} {x y : Fin (suc s)} {e1 e2 : Term (suc s)} -> Abs e1 ≡ Abs e2 -> e1 ≡ e2
absInj2 refl = refl

-- lookupCtx : {{R : Semiring}} -> {s : ℕ} -> (Γ : Context s) -> Fin s -> Assumption
-- lookupCtx (Ext ctx x₁) Fin.zero = x₁
-- lookupCtx (Ext ctx x₁) (Fin.suc x) = lookupCtx ctx x

-------------------------------------------------
-- # Typing

-- raise on the right
raiseR : ∀ {m} n → Fin m → Fin (m + n)
raiseR {m} n i rewrite +-comm m n = raise n i

data _⊢_∶_ {{R : Semiring}} : {s : ℕ} -> Context s -> Term s -> Type -> Set where

--  (x : A) ∈ Γ
----------------------------
--  Γ |- x : A

  var : {s1 s2 : ℕ}
        { A : Type }
        { Γ : Context (s1 + 1 + s2) }
        { Γ1 : Context s1 }
        { Γ2 : Context s2 }
        (pos : Γ ≡ ((Ext (0R · Γ1) (Grad A 1R)) ,, (0R · Γ2)))
    ->  ---------------------
        Γ ⊢ Var (raiseR s2 (fromℕ s1)) ∶ A


  app : {s : ℕ}
        { Γ Γ1 Γ2 : Context s }
        { r : grade }
        { A B : Type}
        { t1 t2 : Term s }

     ->   Γ1 ⊢ t1 ∶ FunTy A r B
     ->   Γ2 ⊢ t2 ∶ A
     ->   { Γ ≡ (Γ1 ++ (r · Γ2))}
     -> -----------------------------
          Γ ⊢ App t1 t2 ∶ B


  abs : {s1 s2 : ℕ}
        { Γ : Context (s1 + 1 + s2) }
        { Γ1 : Context s1 }
        { Γ2 : Context s2 }
        { Γ' : Context (s1 + s2) }
        { r : grade }
        { A B : Type }
        { t : Term (s1 + 1 + s2) }

      -> (pos : Γ ≡ (Ext Γ1 (Grad A r)) ,, Γ2) -- TODO: why are we splitting into G1 and G2? aren't we adding the new variable at the end of G?
      -> Γ ⊢ t ∶ B
      -> { Γ' ≡ (Γ1 ,, Γ2)}
      -> --------------------------------------
         Γ' ⊢ Abs t ∶ FunTy A r B -- TODO: double-check x


  pr : {s : ℕ}
    -> { Γ Γ' : Context s }
    -> { r : grade }
    -> { A : Type }
    -> { t : Term s }

    -> Γ ⊢ t ∶ A
    -> { Γ' ≡ r · Γ }
    --------------------------------
    -> Γ' ⊢ Promote t ∶ Box r A


  unbox : {s : ℕ}
      -> { Γ1 Γ2 Γ : Context s }
      -> { r : grade }
      -> { A B : Type }
      -> (t1 : Term s)
      -> (t2 : Term (suc s))
      -> (Γ1 ⊢ t1 ∶ Box r A)
      -> Ext Γ2 (Grad A r) ⊢ t2 ∶ B
      -> { Γ ≡ Γ1 ++ Γ2 }
      -> --------------------------
         Γ ⊢ Let t1 t2 ∶ B

  unitConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0R · Γ) ⊢ unit ∶ Unit

  trueConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0R · Γ) ⊢ vtrue ∶ BoolTy

  falseConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0R · Γ) ⊢ vfalse ∶ BoolTy

  if : {s : ℕ}
       { Γ Γ1 Γ2 : Context s }
       { B : Type }
       { t1 t2 t3 : Term s }
       { r : grade }
       { used : r ≤ 1R }

    -> Γ1 ⊢ t1 ∶ BoolTy
    -> Γ2 ⊢ t2 ∶ B
    -> Γ2 ⊢ t3 ∶ B
    -> { res : ((r · Γ1) ++ Γ2) ≡ Γ }
   ----------------------------------
    -> Γ ⊢ If t1 t2 t3 ∶ B


-- # Operational semantics

-- Value predicate
data Value : {s : ℕ} -> Term s -> Set where
  unitValue    : Value unit
  varValue     : {s : ℕ} -> Value (Var (fromℕ s))
  absValue     : {s : ℕ} -> (t : Term (suc s)) -> Value (Abs t)
  promoteValue : {s : ℕ} -> (t : Term s) -> Value (Promote t)
  trueValue    : Value vtrue
  falseValue   : Value vfalse

-- -- Substitution lemma
-- -- TODO: Vilem
-- substitution : {{R : Semiring}} {s1 s2 : ℕ} {Γ : Context ((1 + s1) + s2)} {Γ1 : Context s1} {Γ2 : Context (s1 + s2)} {Γ3 : Context s2} {r : grade} {A B : Type} {t1 t2 : Term}
--       -> Γ ⊢ t1 ∶ B
--       -> (pos : Γ ≡ ((Ext Γ1 (Grad A r)) ,, Γ3))
--       -> Γ2 ⊢ t2 ∶ A
--       -> ((Γ1 ,, Γ3) ++ (r · Γ2)) ⊢ syntacticSubst t2 (Γlength Γ1) t1 ∶ B

-- --substitution {Γ1} {Γ2} {.1r} {A} {.A} {Var .0} {t2} (var (Here .Γ1 .A (Γ1' , allZeroesPrf))) substitee
-- --  rewrite allZeroesPrf | absorptionContext {Γ1'} {1r · Γ2} | leftUnitContext {Γ2} =
-- --    t2 , substitee

-- substitution {Γ} {Γ1} {Γ2} {Γ3} {r} {A} {B} {t1} {t2} substitutee pos e = {!subs!}


-- -- Progress lemma
-- redux : {{R : Semiring}} {s : ℕ} {Γ : Context s} {A : Type} {t : Term}
--       -> Γ ⊢ t ∶ A
--       -> (Value t) ⊎ ∃ (\t' -> Γ ⊢ t' ∶ A)

-- redux {{_}} {s} {Γ} {A} {Var _} (var pos) = inj₁ varValue

-- -- Beta
-- --
-- --        deriv1 =  Γ₁ ⊢ t ∶ A
-- --        Γ₁ = Ext (Γ1 ,, Γ2) (Grad A₁ r)
-- --      --------------------------
-- --            (\× . t) t2
-- --
-- redux {{_}} {s} {Γ} {A} {.(App (Abs _ _) _)} (app {t2 = t2} (abs {t = t} pos deriv1) deriv2 {ctxtPrf}) rewrite ctxtPrf  =
--   let derive' = substitution deriv1 pos deriv2
--   in inj₂ (syntacticSubst t2 {!!} t , {!derive'!})

-- redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) with redux deriv1
-- redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 with redux deriv2
-- redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₁ v2 = inj₁ {!!}

-- redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₂ (t2' , deriv2') = inj₂ (App t1 t2' , app deriv1 deriv2')

-- redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₂ (t1' , deriv1') = inj₂ (App t1' t2 , app deriv1' deriv2)

-- redux {{_}} {s} {Γ} {.(FunTy _ _ _)} {(Abs n t)} (abs pos deriv) with redux deriv
-- ... | inj₁ v = inj₁ {!!}
-- ... | inj₂ (t' , deriv') = inj₂ (Abs n t' , abs pos deriv')

-- redux {{_}} {s} {Γ} {A} {unit} _ = inj₁ unitValue
-- redux {{_}} {s} {Γ} {A} {t} t1 = {!!}


-- Untyped reduction
untypedRedux : {s : ℕ} -> Term s -> Maybe (Term s)
untypedRedux (App (Abs t) t') = just (syntacticSubst t' Data.Fin.zero t)
untypedRedux (App t1 t2) with untypedRedux t1
... | just t1' = just (App t1' t2)
... | nothing  = nothing
untypedRedux (If vtrue t1 _) = just t1
untypedRedux (If vfalse _ t2) = just t2
untypedRedux (If t t1 t2) with untypedRedux t
... | just t' = just (If t' t1 t2)
... | nothing = nothing
untypedRedux _ = nothing

{-# TERMINATING #-}
multiRedux : {s : ℕ} -> Term s -> Term s
multiRedux t with untypedRedux t
... | just t' = multiRedux t'
... | nothing = t

determinism : {t t1 t2 : Term s}
             -> multiRedux t ≡ t1
             -> multiRedux t ≡ t2
             -> t1 ≡ t2
determinism prf1 prf2 = trans (sym prf1) prf2             

postulate
   valuesDontReduce : {s : ℕ} {t : Term s} -> Value t -> multiRedux t ≡ t


-- multiReduxProducesValues : {{R : Semiring}} {A : Type} {t : Term} -> Empty ⊢ t ∶ A -> Value (multiRedux t)
-- multiReduxProducesValues {A} {Var _} ()
-- multiReduxProducesValues {A} {App t1 t2} (app typing1 typing2) = {!!}
-- multiReduxProducesValues {FunTy _ _ _} {Abs x t} _
--   with untypedRedux (Abs x t) | inspect untypedRedux (Abs x t)
-- ... | just t' | [ () ]
-- ... | nothing | [ prf ] = absValue {x} t
-- multiReduxProducesValues {A} {unit} typing = unitValue
-- multiReduxProducesValues {A} {Promote t} typing = promoteValue t
-- multiReduxProducesValues {A} {vtrue} typing = trueValue
-- multiReduxProducesValues {A} {vfalse} typing = falseValue
-- multiReduxProducesValues {A} {If t t₁ t₂} typing = {!!}

postulate
  multReduxCongruence : {t1 v : Term s} {C : Term s -> Term s}
                   -> multiRedux t1 ≡ v -> multiRedux (C t1) ≡ multiRedux (C v)

  preservation : {{R : Semiring}} {Γ : Context s} {A : Type} {t : Term s}
             -> Γ ⊢ t ∶ A
             -> Γ ⊢ multiRedux t ∶ A

-- # Equality

data FullBetaEq : Term s -> Term s -> Set where
  VarEq     : {x : Fin (suc s)} -> FullBetaEq (Var x) (Var x)
  AppEq     : {t1 t1' t2 t2' : Term s} -> FullBetaEq t1 t1' -> FullBetaEq t2 t2' -> FullBetaEq (App t1 t2) (App t1' t2')
  AbsEq     : {t1 t2 : Term (suc s)} -> FullBetaEq t1 t2 -> FullBetaEq (Abs t1) (Abs t2)
  UnitEq    : FullBetaEq (unit {s}) (unit {s})
  PromoteEq : {t1 t2 : Term s} -> FullBetaEq t1 t2 -> FullBetaEq (Promote t1) (Promote t2)
  VTrue     : FullBetaEq (vtrue {s}) (vtrue {s})
  VFalse    : FullBetaEq (vfalse {s}) (vfalse {s})
  IfEq      : {t t' t1 t1' t2 t2' : Term s} -> FullBetaEq t t' -> FullBetaEq t1 t1' -> FullBetaEq t2 t2'
               -> FullBetaEq (If t t1 t2) (If t' t1' t2')
  BetaEq    : {t1 : Term (suc s)} {t2 : Term s} -> FullBetaEq (App (Abs t1) t2) (syntacticSubst t2 Data.Fin.zero t1)
  EmbedRedux : {t : Term s} -> FullBetaEq (multiRedux t) t
  LetEq     : {t1 t1' : Term s} {t2 t2' : Term (suc s)} -> FullBetaEq t1 t1' -> FullBetaEq t2 t2' -> FullBetaEq (Let t1 t2) (Let t1' t2')

_==_ : Term s -> Term s -> Set
t == t' = FullBetaEq t t'

embedReduxCong : {t1 t2 : Term s} -> multiRedux t1 ≡ multiRedux t2 -> FullBetaEq t1 t2
embedReduxCong = {!!}

embedEq : {t1 t2 : Term s} -> t1 ≡ t2 -> FullBetaEq t1 t2
embedEq {_} {Var x} {Var .x} refl = VarEq
embedEq {_} {App t1 t2} {App .t1 .t2} refl = AppEq (embedEq {_} {t1} {t1} refl) (embedEq {_} {t2} {t2} refl)
embedEq {_} {Abs t1} {Abs t2} prf = {!!}
embedEq {_} {unit} {unit} refl = UnitEq {_}
embedEq {_} {Promote t1} {Promote .t1} refl = PromoteEq (embedEq {_} {t1} {t1} refl)
embedEq {_} {vtrue} {vtrue} refl = VTrue {_}
embedEq {_} {vfalse} {vfalse} refl = VFalse {_}
embedEq {_} {If t1 t2 t3} {If .t1 .t2 .t3} refl =
  IfEq (embedEq {_} {t1} {t1} refl) (embedEq {_} {t2} {t2} refl) (embedEq {_} {t3} {t3} refl)
embedEq {_} {Let e1 e2} {Let e3 e4} refl = LetEq ((embedEq {_} {e1} {e3} refl)) ( (embedEq {_} {e2} {e4} refl))

-- transFullBetaEq : {t1 t2 t3 : Term} -> t1 == t2 -> t2 == t3 -> t1 == t3
-- transFullBetaEq = {!!}
