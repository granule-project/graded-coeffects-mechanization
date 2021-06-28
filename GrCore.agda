
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
open import Data.Unit hiding (_≟_; _≤_)

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

boolToSet : Bool -> Set
boolToSet false = ⊥
boolToSet true = ⊤

invProperty : {r s adv : Semiring} -> boolToSet ((r *R s) ≤ adv) -> boolToSet (s ≤ adv)
invProperty {Hi} {Hi} {Hi} pre = tt
invProperty {Hi} {Lo} {Hi} pre = tt
invProperty {Lo} {Hi} {Hi} pre = tt
invProperty {Lo} {Lo} {Hi} pre = tt
invProperty {Lo} {Lo} {Lo} pre = tt

invPropertyA : {r s adv : Semiring} -> ((r *R s) ≤ adv) ≡ true -> (s ≤ adv) ≡ true
invPropertyA {Hi} {Hi} {Hi} pre = refl
invPropertyA {Hi} {Lo} {Hi} pre = refl
invPropertyA {Lo} {Hi} {Hi} pre = pre
invPropertyA {Lo} {Lo} {Hi} pre = refl
invPropertyA {Lo} {Lo} {Lo} pre = refl

invPropertyB : {r s adv : Semiring} -> ((r *R s) ≤ adv) ≡ false -> (s ≤ adv) ≡ false
invPropertyB {Hi} {Hi} {Lo} pre = refl
-- Hi * Lo <= Lo  is  Hi <= Lo which is false but Lo <= Lo is true
invPropertyB {Hi} {Lo} {Lo} pre = {!!}
invPropertyB {Lo} {Hi} {Lo} pre = refl
invPropertyB {Hi} {Hi} {Hi} pre = pre
invPropertyB {Hi} {Lo} {Hi} pre = pre
invPropertyB {Lo} {Hi} {Hi} pre = pre
invPropertyB {Lo} {Lo} {Hi} pre = pre
invPropertyB {Lo} {Lo} {Lo} pre = pre

invPropertyC : {r s adv : Semiring} -> ((r *R s) ≤ adv) ≡ false -> (r ≤ adv) ≡ true -> (s ≤ adv) ≡ false
invPropertyC {Hi} {Hi} {Hi} () pre2
invPropertyC {Hi} {Hi} {Lo} refl ()
invPropertyC {Hi} {Lo} {Hi} () pre2
invPropertyC {Hi} {Lo} {Lo} refl ()
invPropertyC {Lo} {Hi} {Hi} () pre2
invPropertyC {Lo} {Hi} {Lo} refl refl = refl
invPropertyC {Lo} {Lo} {Hi} () pre2
invPropertyC {Lo} {Lo} {Lo} () pre2

invPropertyD : {r s adv : Semiring} -> (r ≤ adv) ≡ false -> ((r *R s) ≤ adv) ≡ false
invPropertyD {Hi} {Hi} {Lo}  pre = pre
invPropertyD {Hi} {Lo} {Lo}  pre = refl
invPropertyD {Lo} {Hi} {Hi} ()
invPropertyD {Lo} {Hi} {Lo} ()
invPropertyD {Lo} {Lo} {Hi} ()
invPropertyD {Lo} {Lo} {Lo} ()

invPropertyI : {r s adv : Semiring} -> boolToSet (s ≤ adv) -> boolToSet ((r *R s) ≤ adv)
invPropertyI {Hi} {Hi} {Hi} pre = tt
invPropertyI {Hi} {Lo} {Hi} pre = tt
-- Lo <= Lo  but Hi * Lo <= Lo is false.
invPropertyI {Hi} {Lo} {Lo} pre = {!!}
invPropertyI {Lo} {Hi} {Hi} pre = tt
invPropertyI {Lo} {Lo} {Hi} pre = tt
invPropertyI {Lo} {Lo} {Lo} pre = tt

invPropertyE' : {r1 r2 r adv : Semiring} -> boolToSet (r1 ≤ adv) -> boolToSet ((r1 +R (r *R r2)) ≤ adv)
invPropertyE' {Hi} {Hi} {Hi} {Hi} pre = tt
invPropertyE' {Hi} {Hi} {Lo} {Hi} pre = tt
invPropertyE' {Hi} {Lo} {Hi} {Hi} pre = tt
invPropertyE' {Hi} {Lo} {Lo} {Hi} pre = tt
invPropertyE' {Lo} {Hi} {Hi} {Hi} pre = tt
invPropertyE' {Lo} {Hi} {Hi} {Lo} pre = tt
invPropertyE' {Lo} {Hi} {Lo} {Hi} pre = tt
invPropertyE' {Lo} {Hi} {Lo} {Lo} pre = tt
invPropertyE' {Lo} {Lo} {Hi} {Hi} pre = tt
invPropertyE' {Lo} {Lo} {Hi} {Lo} pre = tt
invPropertyE' {Lo} {Lo} {Lo} {Hi} pre = tt
invPropertyE' {Lo} {Lo} {Lo} {Lo} pre = tt

invPropertyF : {r1 r2 r adv : Semiring} -> ((r1 +R (r *R r2)) ≤ adv) ≡ false -> (r1 ≤ adv) ≡ false
invPropertyF {Hi} {Hi} {Hi} {Hi} ()
invPropertyF {Hi} {Hi} {Lo} {Hi} ()
invPropertyF {Hi} {Lo} {Hi} {Hi} ()
invPropertyF {Hi} {Lo} {Lo} {Hi} ()
invPropertyF {Hi} {Lo} {Lo} {Lo} ()
invPropertyF {Lo} {Hi} {Hi} {Hi} ()
invPropertyF {Lo} {Hi} {Hi} {Lo} ()
invPropertyF {Lo} {Hi} {Lo} {Hi} ()
invPropertyF {Lo} {Hi} {Lo} {Lo} ()
invPropertyF {Lo} {Lo} {Hi} {Hi} ()
invPropertyF {Lo} {Lo} {Hi} {Lo} ()
invPropertyF {Lo} {Lo} {Lo} {Hi} ()
invPropertyF {Lo} {Lo} {Lo} {Lo} ()
invPropertyF {Hi} {Hi} {Hi} {Lo} refl = refl
invPropertyF {Hi} {Hi} {Lo} {Lo} refl = refl
invPropertyF {Hi} {Lo} {Hi} {Lo} refl = refl

invPropertyF2 : {r1 r2 r adv : Semiring} -> ((r1 +R (r *R r2)) ≤ adv) ≡ false -> (r2 ≤ adv) ≡ false
invPropertyF2 {Hi} {Hi} {Hi} {Lo} pre = refl
invPropertyF2 {Hi} {Hi} {Lo} {Lo} pre = refl
-- Hi + Lo * Hi <= Lo
-- Hi + Hi <= Lo
-- Hi <= Lo FALSE

-- but
-- Lo <= Lo TRUE
invPropertyF2 {Hi} {Lo} {Hi} {Lo} pre = {!!}
invPropertyF2 {Hi} {Hi} {Hi} {Hi} ()
invPropertyF2 {Hi} {Hi} {Lo} {Hi} ()
invPropertyF2 {Hi} {Lo} {Hi} {Hi} ()
invPropertyF2 {Hi} {Lo} {Lo} {Hi} ()
invPropertyF2 {Hi} {Lo} {Lo} {Lo} ()
invPropertyF2 {Lo} {Hi} {Hi} {Hi} ()
invPropertyF2 {Lo} {Hi} {Hi} {Lo} ()
invPropertyF2 {Lo} {Hi} {Lo} {Hi} ()
invPropertyF2 {Lo} {Hi} {Lo} {Lo} ()
invPropertyF2 {Lo} {Lo} {Hi} {Hi} ()
invPropertyF2 {Lo} {Lo} {Hi} {Lo} ()
invPropertyF2 {Lo} {Lo} {Lo} {Hi} ()
invPropertyF2 {Lo} {Lo} {Lo} {Lo} ()

invPropertG : {r1 r2 r adv : Semiring}  -> ((r1 +R (r *R r2)) ≤ adv) ≡ true
                                        -> (r2 ≤ adv) ≡ true
invPropertG {Hi} {Hi} {Hi} {Hi} pre = refl
invPropertG {Hi} {Hi} {Lo} {Hi} pre = refl
invPropertG {Hi} {Lo} {Hi} {Hi} pre = refl
invPropertG {Hi} {Lo} {Lo} {Hi} pre = refl
invPropertG {Hi} {Lo} {Lo} {Lo} pre = refl
invPropertG {Lo} {Hi} {Hi} {Hi} pre = refl
invPropertG {Lo} {Hi} {Hi} {Lo} pre = {!!}
invPropertG {Lo} {Hi} {Lo} {Hi} pre = {!!}
invPropertG {Lo} {Hi} {Lo} {Lo} pre = {!!}
invPropertG {Lo} {Lo} {Hi} {Hi} pre = {!!}
invPropertG {Lo} {Lo} {Hi} {Lo} pre = {!!}
invPropertG {Lo} {Lo} {Lo} {Hi} pre = {!!}
invPropertG {Lo} {Lo} {Lo} {Lo} pre = {!!}

invPropertyE : {r1 r2 r adv : Semiring} -> boolToSet ((r1 +R (r *R r2)) ≤ adv) -> boolToSet (r1 ≤ adv)
invPropertyE {Hi} {Hi} {Hi} {Hi} pre = tt
invPropertyE {Hi} {Hi} {Lo} {Hi} pre = tt
invPropertyE {Hi} {Lo} {Hi} {Hi} pre = tt
invPropertyE {Hi} {Lo} {Lo} {Hi} pre = tt
-- not good.
--    Hi + (Lo * Lo) <= Lo
--    Hi + Lo <= Lo
--    Lo <= Lo yes
-- vs.
--    Hi <= Lo  false
invPropertyE {Hi} {Lo} {Lo} {Lo} pre = {!!}
invPropertyE {Lo} {Hi} {Hi} {Hi} pre = tt
invPropertyE {Lo} {Hi} {Hi} {Lo} pre = tt
invPropertyE {Lo} {Hi} {Lo} {Hi} pre = tt
invPropertyE {Lo} {Hi} {Lo} {Lo} pre = tt
invPropertyE {Lo} {Lo} {Hi} {Hi} pre = tt
invPropertyE {Lo} {Lo} {Hi} {Lo} pre = tt
invPropertyE {Lo} {Lo} {Lo} {Hi} pre = tt
invPropertyE {Lo} {Lo} {Lo} {Lo} pre = tt

invPropertyHo : {r1 r2 r adv : Semiring}  -> ((r1 +R (r *R r2)) ≤ adv) ≡ false -> (r2 ≤ adv) ≡ true -> (r ≤ adv) ≡ false -> ⊥
invPropertyHo {Hi} {Lo} {Hi} {Lo} pre1 pre2 pre3 = ?
invPropertyHo {_} {_} {_} {_} () () ()

invPropertH : {r1 r2 r adv : Semiring}  -> ((r1 +R (r *R r2)) ≤ adv) ≡ false -> (r2 ≤ adv) ≡ true -> ⊥
invPropertH {Hi} {Hi} {Hi} {Lo} refl ()
invPropertH {Hi} {Hi} {Lo} {Lo} refl ()
-- Hi + (Hi * Lo) <= Lo
-- Hi + Hi <= Lo
-- Hi <= Lo  FALSE

-- Lo <= Lo  TRUE hm.

invPropertH {Hi} {Lo} {Hi} {Lo} refl refl = {!!}
invPropertH {Hi} {Hi} {Hi} {Hi} pre pre2 = {!!}
invPropertH {Hi} {Hi} {Lo} {Hi} pre pre2 = {!!}
invPropertH {Hi} {Lo} {Hi} {Hi} pre pre2 = {!!}
invPropertH {Hi} {Lo} {Lo} {Hi} pre pre2 = {!!}
invPropertH {Hi} {Lo} {Lo} {Lo} pre pre2 = {!!}
invPropertH {Lo} {Hi} {Hi} {Hi} pre pre2 = {!!}
invPropertH {Lo} {Hi} {Hi} {Lo} pre pre2 = {!!}
invPropertH {Lo} {Hi} {Lo} {Hi} pre pre2 = {!!}
invPropertH {Lo} {Hi} {Lo} {Lo} pre pre2 = {!!}
invPropertH {Lo} {Lo} {Hi} {Hi} pre pre2 = {!!}
invPropertH {Lo} {Lo} {Hi} {Lo} pre pre2 = {!!}
invPropertH {Lo} {Lo} {Lo} {Hi} pre pre2 = {!!}
invPropertH {Lo} {Lo} {Lo} {Lo} pre pre2 = {!!}

infFlo : {r s adv : Semiring} -> ¬ (boolToSet ((r *R s) ≤ adv))
                           -> boolToSet (s ≤ adv)
                           -> ⊥
infFlo {Hi} {Hi} {Hi} narg arg = narg arg
infFlo {Hi} {Lo} {Hi} narg arg = narg tt
-- Hi * Lo = Hi   <= Lo   false
-- but
--    Lo <= Lo   true
--
infFlo {Hi} {Lo} {Lo} narg arg = {!!}
infFlo {Lo} {Hi} {Hi} narg arg = {!!}
infFlo {Lo} {Lo} {Hi} narg arg = {!!}
infFlo {Lo} {Lo} {Lo} narg arg = {!!}

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

data Context : ℕ -> Set where
  Empty   : Context 0
  Ext     : {n : ℕ} -> Context n -> Assumption -> Context (1 + n)

injExt1 : {s : ℕ} {Γ Γ' : Context s} {A A' : Assumption} -> Ext Γ A ≡ Ext Γ' A' -> Γ ≡ Γ'
injExt1 refl = refl

injExt2 : {s : ℕ} {Γ Γ' : Context s} {A A' : Assumption} -> Ext Γ A ≡ Ext Γ' A' -> A ≡ A'
injExt2 refl = refl

-- Disjoint context concatentation
_,,_ : {s t : ℕ} -> Context s -> Context t -> Context (s + t)
Empty      ,, G2 = G2
(Ext G1 a) ,, G2 = Ext (G1 ,, G2) a
--G1 ,, Empty = G1
--G1 ,, (Ext G2 a) = Ext (G1 ,, G2) a

-- Context scalar multiplication
_·_ : {s : ℕ} -> Semiring -> Context s -> Context s
r · Empty = Empty
r · Ext g (Grad A s) = Ext (r · g) (Grad A (r *R s))

-- Context addition
_++_ : {s : ℕ} -> Context s -> Context s -> Context s
Empty ++ Empty = Empty
(Ext G (Grad A r)) ++ (Ext G' (Grad B s)) = Ext (G ++ G') (Grad A (r +R s))

postulate
  absorptionContext : {s : ℕ} {Γ Γ' : Context s} -> (0r · Γ) ++ Γ' ≡ Γ'
  leftUnitContext : {s : ℕ} {Γ : Context s} -> 1r · Γ ≡ Γ

Γlength : {s : ℕ} -> Context s -> ℕ
Γlength Empty = 0
Γlength (Ext g a) = 1 + Γlength g

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
data _⊢_∶_ : {s : ℕ} -> Context s -> Term -> Type -> Set where

--  (x : A) ∈ Γ
----------------------------
--  Γ |- x : A

  var : {s1 s2 : ℕ}
        { A : Type }
        { Γ : Context ((1 + s1) + s2) }
        { Γ1 : Context s1 }
        { Γ2 : Context s2 }
        (pos : Γ ≡ ((Ext (0r · Γ1) (Grad A 1r)) ,, (0r · Γ2)))
    ->  ---------------------
        Γ ⊢ Var (Γlength Γ1) ∶ A


  app : {s : ℕ}
        { Γ Γ1 Γ2 : Context s }
        { r : Semiring }
        { A B : Type}
        { t1 t2 : Term }

     ->   Γ1 ⊢ t1 ∶ FunTy A r B
     ->   Γ2 ⊢ t2 ∶ A
     ->   { Γ ≡ (Γ1 ++ (r · Γ2))}
     -> -----------------------------
          Γ ⊢ App t1 t2 ∶ B


  abs : {s1 s2 : ℕ}
        { Γ : Context ((1 + s1) + s2) }
        { Γ1 : Context s1 }
        { Γ2 : Context s2 }
        { Γ' : Context (s1 + s2) }
        { r : Semiring}
        { A B : Type }
        { t : Term }

      -> (pos : Γ ≡ (Ext Γ1 (Grad A r)) ,, Γ2)
      -> Γ ⊢ t ∶ B
      -> { Γ' ≡ (Γ1 ,, Γ2)}
      -> --------------------------------------
         Γ' ⊢ Abs (Γlength Γ1 + 1) t ∶ FunTy A r B


  pr : {s : ℕ}
    -> { Γ Γ' : Context s }
    -> { r : Semiring }
    -> { A : Type }
    -> { t : Term }

    -> Γ ⊢ t ∶ A
    -> { Γ' ≡ r · Γ }
    --------------------------------
    -> Γ' ⊢ Promote t ∶ Box r A


  unitConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0r · Γ) ⊢ unit ∶ Unit

  trueConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
           (0r · Γ) ⊢ vtrue ∶ BoolTy

  falseConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
           (0r · Γ) ⊢ vfalse ∶ BoolTy

  if : {s : ℕ}
       { Γ1 Γ2 : Context s }
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
substitution : {s1 s2 : ℕ} {Γ : Context ((1 + s1) + s2)} {Γ1 : Context s1} {Γ2 : Context (s1 + s2)} {Γ3 : Context s2} {r : Semiring} {A B : Type} {t1 t2 : Term}
      -> Γ ⊢ t1 ∶ B
      -> (pos : Γ ≡ ((Ext (0r · Γ1) (Grad A r)) ,, (0r · Γ3)))
      -> Γ2 ⊢ t2 ∶ A
      -> ((Γ1 ,, Γ3) ++ (r · Γ2)) ⊢ syntacticSubst t2 (Γlength Γ1) t1 ∶ B

--substitution {Γ1} {Γ2} {.1r} {A} {.A} {Var .0} {t2} (var (Here .Γ1 .A (Γ1' , allZeroesPrf))) substitee
--  rewrite allZeroesPrf | absorptionContext {Γ1'} {1r · Γ2} | leftUnitContext {Γ2} =
--    t2 , substitee

substitution {Γ} {Γ1} {Γ2} {Γ3} {r} {A} {B} {t1} {t2} substitutee pos e = {!subs!}


-- constructive progress
redux : {s : ℕ} {Γ : Context s} {A : Type} {t : Term}
      -> Γ ⊢ t ∶ A
      -> (Value t) ⊎ ∃ (\t' -> Γ ⊢ t' ∶ A)

redux {s} {Γ} {A} {Var _} (var _) = inj₁ varValue

redux {s} {Γ} {A} {.(App (Abs _ _) _)} (app (abs pos deriv) deriv₁) = {!!}

redux {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) with redux deriv1
redux {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 with redux deriv2
redux {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₁ v2 = inj₁ {!!}

redux {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₂ (t2' , deriv2') = inj₂ (App t1 t2' , app deriv1 deriv2')

redux {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₂ (t1' , deriv1') = inj₂ (App t1' t2 , app deriv1' deriv2)

redux {s} {Γ} {.(FunTy _ _ _)} {(Abs n t)} (abs pos deriv) with redux deriv
... | inj₁ v = inj₁ {!!}
... | inj₂ (t' , deriv') = inj₂ (Abs n t' , abs pos deriv')

redux {s} {Γ} {A} {unit} _ = inj₁ unitValue
redux {s} {Γ} {A} {t} t1 = {!!}

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
multiReduxProducesValues {A} {Var _} ()
multiReduxProducesValues {A} {App t1 t2} (app typing1 typing2) = {!!}
multiReduxProducesValues {FunTy _ _ _} {Abs x t} _
  with untypedRedux (Abs x t) | inspect untypedRedux (Abs x t)
... | just t' | [ () ]
... | nothing | [ prf ] = absValue {x} t
multiReduxProducesValues {A} {unit} typing = unitValue
multiReduxProducesValues {A} {Promote t} typing = promoteValue t
multiReduxProducesValues {A} {vtrue} typing = trueValue
multiReduxProducesValues {A} {vfalse} typing = falseValue
multiReduxProducesValues {A} {If t t₁ t₂} typing = {!!}

preservation : {s : ℕ} {Γ : Context s} {A : Type} {t : Term}
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
