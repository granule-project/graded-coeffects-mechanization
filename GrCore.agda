
{-# OPTIONS --allow-unsolved-metas #-}

module GrCore where

open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Maybe
open import Data.Empty

-- Sec
data Semiring : Set where
  Hi : Semiring
  Lo  : Semiring

1r : Semiring
1r = Lo

0r : Semiring
0r = Hi

_+R_ : Semiring -> Semiring -> Semiring
Lo +R _  = Lo
_ +R Lo  = Lo
Hi +R Hi = Hi

_*R_ : Semiring -> Semiring -> Semiring
Hi *R _ = Hi
_ *R Hi = Hi
Lo *R Lo = Lo

leftUnit : {r : Semiring} -> 1r *R r ≡ r
leftUnit {Hi} = refl
leftUnit {Lo} = refl

_≤_ : Semiring -> Semiring -> Bool
_≤_ Lo Hi = true
_≤_ Lo Lo = true
_≤_ Hi Hi = true
_≤_ Hi Lo = false

data Type : Set where
  FunTy : (A : Type) -> (r : Semiring) -> (B : Type) -> Type -- A r -> B
  Unit  : Type
  Box   : (r : Semiring) -> Type -> Type
  --------------------------------------------------
  -- Prod  : Type -> Type -> Type
  -- Sum   : Type -> Type -> Type
  BoolTy : Type


data Assumption : Set where
--  Lin : (A : Type)                    -> Assumption A
  Grad : (A : Type) -> (r : Semiring) -> Assumption

injGradTy : {A A' : Type} {r r' : Semiring} -> Grad A r ≡ Grad A' r' -> A ≡ A'
injGradTy refl = refl

injGradR : {A A' : Type} {r r' : Semiring} -> Grad A r ≡ Grad A' r' -> r ≡ r'
injGradR refl = refl

data Context : Set where
  Empty   : Context
  Ext     : Context -> Assumption -> Context

injExt1 : {Γ Γ' : Context} {A A' : Assumption} -> Ext Γ A ≡ Ext Γ' A' -> Γ ≡ Γ'
injExt1 refl = refl

injExt2 : {Γ Γ' : Context} {A A' : Assumption} -> Ext Γ A ≡ Ext Γ' A' -> A ≡ A'
injExt2 refl = refl

_,,_ : Context -> Context -> Context
Empty      ,, G2 = G2
(Ext G1 a) ,, G2 = Ext (G1 ,, G2) a

_·_ : Semiring -> Context -> Context
r · Empty = Empty
r · Ext g (Grad A s) = Ext (r · g) (Grad A (r *R s))

-- Make contexts a module
postulate
  -- TODO
_++_ : Context -> Context -> Context
Empty ++ G = G
G ++ Empty = G
(Ext G (Grad A r)) ++ (Ext G' (Grad B s)) = Ext (G ++ G') (Grad A (r +R s))
G' ++ G'' = {!!}

postulate
  absorptionContext : {Γ Γ' : Context} -> (0r · Γ) ++ Γ' ≡ Γ'
  leftUnitContext : {Γ : Context} -> 1r · Γ ≡ Γ

Γlength : Context -> ℕ
Γlength Empty = 0
Γlength (Ext g _) = 1 + Γlength g

data Term : Set where
  Var : ℕ -> Term
  App : Term -> Term -> Term
  Abs : ℕ -> Term -> Term
  unit : Term
  Promote : Term -> Term
  -- handling bools (TODO: generalise to sums)
  vtrue : Term
  vfalse : Term
  If : Term -> Term -> Term -> Term

syntacticSubst : Term -> ℕ -> Term -> Term
syntacticSubst t x (Var y) with x ≟ y
... | yes p = t
... | no ¬p = Var y
syntacticSubst t x (App t1 t2) = App (syntacticSubst t x t1) (syntacticSubst t x t2)
syntacticSubst t x (Abs y t1) with x ≟ y
... | yes p = Abs y t1
... | no ¬p = Abs y (syntacticSubst t x t1)
syntacticSubst t x (Promote t1) = Promote (syntacticSubst t x t1)
syntacticSubst t x unit = unit
syntacticSubst t x vtrue = vtrue
syntacticSubst t x vfalse = vfalse
syntacticSubst t x (If t1 t2 t3) = If (syntacticSubst t x t1) (syntacticSubst t x t2) (syntacticSubst t x t3)



-------------------------------------------------
-- Typing
data _⊢_∶_ : Context -> Term -> Type -> Set where

--  (x : A) ∈ Γ
----------------------------
--  Γ |- x : A

  var : { A : Type }
        { Γ Γ1 Γ2 : Context }
        (pos : Γ ≡ ((Ext (0r · Γ1) (Grad A 1r)) ,, (0r · Γ2)))
    ->  ---------------------
        Γ ⊢ Var (Γlength Γ1) ∶ A


  app : { Γ Γ1 Γ2 : Context }
        { r : Semiring }
        { A B : Type}
        { t1 t2 : Term }

     ->   Γ1 ⊢ t1 ∶ FunTy A r B
     ->   Γ2 ⊢ t2 ∶ A
     ->   { Γ ≡ (Γ1 ++ (r · Γ2))}
     -> -----------------------------
          Γ ⊢ App t1 t2 ∶ B


  abs : { Γ Γ1 Γ2 Γ' : Context }
        { r : Semiring}
        { A B : Type }
        { t : Term }

      -> (pos : Γ ≡ (Ext Γ1 (Grad A r)) ,, Γ2)
      -> Γ ⊢ t ∶ B
      -> { Γ' ≡ (Γ1 ,, Γ2)}
      -> --------------------------------------
         Γ' ⊢ Abs (Γlength Γ1 + 1) t ∶ FunTy A r B


  pr : { Γ Γ' : Context }
    -> { r : Semiring }
    -> { A : Type }
    -> { t : Term }

    -> Γ ⊢ t ∶ A
    -> { Γ' ≡ r · Γ }
    --------------------------------
    -> Γ' ⊢ Promote t ∶ Box r A


  unitConstr : { Γ : Context }
      -> --------------------------------
          (0r · Γ) ⊢ unit ∶ Unit

  trueConstr : { Γ : Context }
      -> --------------------------------
           (0r · Γ) ⊢ vtrue ∶ BoolTy

  falseConstr : { Γ : Context }
      -> --------------------------------
           (0r · Γ) ⊢ vfalse ∶ BoolTy

  if : { Γ1 Γ2 : Context }
       { B : Type }
       { t1 t2 t3 : Term }

    -> Γ1 ⊢ t1 ∶ BoolTy
    -> Γ2 ⊢ t2 ∶ B
    -> Γ2 ⊢ t3 ∶ B
   ----------------------------------
    -> (Γ1 ++ Γ2) ⊢ If t1 t2 t3 ∶ B


-- Value predicate
data Value : Term -> Set where
  unitValue    : Value unit
  varValue     : {n : ℕ} -> Value (Var n)
  absValue     : {n : ℕ} -> (t : Term) -> Value (Abs n t)
  promoteValue : (t : Term) -> Value (Promote t)
  trueValue    : Value vtrue
  falseValue   : Value vfalse

-- substitution
substitution : {Γ Γ1 Γ2 Γ3 : Context} {r : Semiring} {A B : Type} {t1 t2 : Term}
      -> Γ ⊢ t1 ∶ B
      -> (pos : Γ ≡ ((Ext (0r · Γ1) (Grad A r)) ,, (0r · Γ2)))
      -> Γ3 ⊢ t2 ∶ A
      -> ((Γ1 ++ (r · Γ2)) ++ Γ3) ⊢ syntacticSubst t2 (Γlength Γ1) t1 ∶ B

--substitution {Γ1} {Γ2} {.1r} {A} {.A} {Var .0} {t2} (var (Here .Γ1 .A (Γ1' , allZeroesPrf))) substitee
--  rewrite allZeroesPrf | absorptionContext {Γ1'} {1r · Γ2} | leftUnitContext {Γ2} =
--    t2 , substitee

substitution {Γ} {Γ1} {Γ2} {Γ3} {r} {A} {B} {t1} {t2} substitutee pos e = {!subs!}


-- constructive progress
redux : {Γ : Context} {A : Type} {t : Term}
      -> Γ ⊢ t ∶ A
      -> (Value t) ⊎ ∃ (\t' -> Γ ⊢ t' ∶ A)

redux {Γ} {A} {Var _} (var _) = inj₁ varValue

redux {Γ} {A} {.(App (Abs _ _) _)} (app (abs pos deriv) deriv₁) = {!!}

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) with redux deriv1
redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 with redux deriv2
redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₁ v2 = inj₁ {!!}

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₂ (t2' , deriv2') = inj₂ (App t1 t2' , app deriv1 deriv2')

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₂ (t1' , deriv1') = inj₂ (App t1' t2 , app deriv1' deriv2)

redux {Γ} {.(FunTy _ _ _)} {(Abs n t)} (abs pos deriv) with redux deriv
... | inj₁ v = inj₁ {!!}
... | inj₂ (t' , deriv') = inj₂ (Abs n t' , abs pos deriv')

redux {Γ} {A} {unit} _ = inj₁ unitValue
redux {Γ} {A} {t} t1 = {!!}

untypedRedux : Term -> Maybe Term
untypedRedux (App (Abs x t) t') = just (syntacticSubst t' x t)
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
multiRedux : Term -> Term
multiRedux t with untypedRedux t
... | just t' = multiRedux t'
... | nothing = t

multiReduxProducesValues : {A : Type} {t : Term} -> Empty ⊢ t ∶ A -> Value (multiRedux t)
multiReduxProducesValues {A} {Var _} (var ())
multiReduxProducesValues {A} {App t1 t2} (app typing1 typing2) = {!!}
multiReduxProducesValues {.(FunTy _ _ _)} {Abs x t} (abs {Γ} {Γ1} refl typing)
  with untypedRedux (Abs x t) | inspect untypedRedux (Abs x t)
... | just t' | [ () ]
... | nothing | [ prf ] = absValue {x} t
multiReduxProducesValues {A} {unit} typing = unitValue
multiReduxProducesValues {A} {Promote t} typing = promoteValue t
multiReduxProducesValues {A} {vtrue} typing = trueValue
multiReduxProducesValues {A} {vfalse} typing = falseValue
multiReduxProducesValues {A} {If t t₁ t₂} typing = {!!}

preservation : {Γ : Context} {A : Type} {t : Term}
             -> Γ ⊢ t ∶ A
             -> Γ ⊢ multiRedux t ∶ A
preservation = {!!}


valuesDontReduce : {t : Term} -> Value t -> multiRedux t ≡ t
valuesDontReduce {t} v = {!!}

data FullBetaEq : Term -> Term -> Set where
  VarEq     : {x : ℕ} -> FullBetaEq (Var x) (Var x)
  AppEq     : {t1 t1' t2 t2' : Term} -> FullBetaEq t1 t1' -> FullBetaEq t2 t2' -> FullBetaEq (App t1 t2) (App t1' t2')
  AbsEq     : {x : ℕ} {t1 t2 : Term} -> FullBetaEq t1 t2 -> FullBetaEq (Abs x t1) (Abs x t2)
  UnitEq    : FullBetaEq unit unit
  PromoteEq : {t1 t2 : Term} -> FullBetaEq t1 t2 -> FullBetaEq (Promote t1) (Promote t2)
  VTrue     : FullBetaEq vtrue vtrue
  VFalse    : FullBetaEq vfalse vfalse
  IfEq      : {t t' t1 t1' t2 t2' : Term} -> FullBetaEq t t' -> FullBetaEq t1 t1' -> FullBetaEq t2 t2'
               -> FullBetaEq (If t t1 t2) (If t' t1' t2')
  BetaEq    : {x : ℕ} {t1 t2 : Term} -> FullBetaEq (App (Abs x t1) t2) (syntacticSubst t1 x t2)
  EmbedRedux : {t : Term} -> FullBetaEq (multiRedux t) t


_==_ : Term -> Term -> Set
t == t' = FullBetaEq t t'

embedReduxCong : {t1 t2 : Term} -> multiRedux t1 ≡ multiRedux t2 -> FullBetaEq t1 t2
embedReduxCong = {!!}

embedEq : {t1 t2 : Term} -> t1 ≡ t2 -> FullBetaEq t1 t2
embedEq {Var x} {Var .x} refl = VarEq
embedEq {App t1 t2} {App .t1 .t2} refl = AppEq (embedEq {t1} {t1} refl) (embedEq {t2} {t2} refl)
embedEq {Abs x t1} {Abs x₁ t2} prf = {!!}
embedEq {unit} {unit} refl = UnitEq
embedEq {Promote t1} {Promote .t1} refl = PromoteEq (embedEq {t1} {t1} refl)
embedEq {vtrue} {vtrue} refl = VTrue
embedEq {vfalse} {vfalse} refl = VFalse
embedEq {If t1 t2 t3} {If .t1 .t2 .t3} refl = IfEq (embedEq {t1} {t1} refl) (embedEq {t2} {t2} refl) (embedEq {t3} {t3} refl)

transFullBetaEq : {t1 t2 t3 : Term} -> t1 == t2 -> t2 == t3 -> t1 == t3
transFullBetaEq = {!!}
