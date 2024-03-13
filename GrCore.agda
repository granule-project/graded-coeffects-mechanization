
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module GrCore where

open import Data.Product
open import Data.Sum
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-comm; +-assoc)
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
  ProdTy  : Type -> Type -> Type
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
-- OLD
--Empty ,, G2 = G2
--(Ext G1 a) ,, G2 = Ext (G1 ,, G2) a

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
  -- handling products
  tuple   : {s : ℕ} -> Term s -> Term s -> Term s
  LetProd : {s : ℕ} -> Term s -> Term (suc (suc s)) -> Term s

raiseTermℕ : (n : ℕ) -> Term s -> Term (n + s)
raiseTermℕ n (Var x) = Var (raise n x)
raiseTermℕ n (App t1 t2) = App (raiseTermℕ n t1) (raiseTermℕ n t2)
raiseTermℕ n (Abs t) = Abs (raiseTermℕ n t)
raiseTermℕ n unit = unit
raiseTermℕ n (Promote t) = Promote (raiseTermℕ n t)
raiseTermℕ n (Let t1 t2) = Let (raiseTermℕ n t1) (raiseTermℕ n t2)
raiseTermℕ n vtrue = vtrue
raiseTermℕ n vfalse = vfalse
raiseTermℕ n (If t t1 t2) = If (raiseTermℕ n t) (raiseTermℕ n t1) (raiseTermℕ n t2)
raiseTermℕ n (tuple t1 t2) = tuple (raiseTermℕ n t1) (raiseTermℕ n t2)
raiseTermℕ n (LetProd t1 t2) = LetProd (raiseTermℕ n t1) (raiseTermℕ n t2)

raiseTermℕzero : {s : ℕ} {t : Term s} -> raiseTermℕ zero t ≡ t
raiseTermℕzero {.(suc _)} {Var x} = refl
raiseTermℕzero {s} {App t1 t2} rewrite raiseTermℕzero {s} {t1} | raiseTermℕzero {s} {t2} = refl
raiseTermℕzero {s} {Abs t} rewrite raiseTermℕzero {suc s} {t} = refl
raiseTermℕzero {s} {unit} = refl
raiseTermℕzero {s} {Promote t} rewrite raiseTermℕzero {s} {t} = refl
raiseTermℕzero {s} {Let t1 t2} rewrite raiseTermℕzero {s} {t1} | raiseTermℕzero {suc s} {t2} = refl
raiseTermℕzero {s} {vtrue} = refl
raiseTermℕzero {s} {vfalse} = refl
raiseTermℕzero {s} {If t0 t1 t2} rewrite raiseTermℕzero {s} {t0} | raiseTermℕzero {s} {t1} | raiseTermℕzero {s} {t2} = refl
raiseTermℕzero {s} {tuple e1 e2} rewrite raiseTermℕzero {s} {e1} | raiseTermℕzero {s} {e2} = refl
raiseTermℕzero {s} {LetProd e1 e2} rewrite raiseTermℕzero {s} {e1} | raiseTermℕzero {suc (suc s)} {e2} = refl

raiseTerm : {s : ℕ} -> Term s -> Term (suc s)
raiseTerm {s} t = raiseTermℕ {s} 1 t

raiseProp : {n : ℕ} {t : Term s} -> raiseTerm (raiseTermℕ n t) ≡ raiseTermℕ (suc n) t
raiseProp {.(suc _)} {n} {Var x} = refl
raiseProp {s} {n} {App t t₁}
  rewrite raiseProp {s} {n} {t} | raiseProp {s} {n} {t₁} = refl
raiseProp {s} {n} {Abs t}
  rewrite raiseProp {suc s} {n} {t} = refl
raiseProp {s} {n} {unit} = refl
raiseProp {s} {n} {Promote t}
  rewrite raiseProp {s} {n} {t} = refl
raiseProp {s} {n} {Let t t₁}
  rewrite raiseProp {s} {n} {t} | raiseProp {suc s} {n} {t₁} = refl
raiseProp {s} {n} {vtrue} = refl
raiseProp {s} {n} {vfalse} = refl
raiseProp {s} {n} {If t t₁ t₂}
  rewrite raiseProp {s} {n} {t} | raiseProp {s} {n} {t₁} | raiseProp {s} {n} {t₂} = refl
raiseProp {s} {n} {tuple e1 e2}
  rewrite raiseProp {s} {n} {e1} | raiseProp {s} {n} {e2} = refl
raiseProp {s} {n} {LetProd e1 e2}
  rewrite raiseProp {s} {n} {e1} | raiseProp {suc (suc s)} {n} {e2} = refl

-- Helper
finRaiseComm : {s n : ℕ} {x : Fin (suc s)} -> Fin.suc (raise n x) ≡ raise n (Fin.suc x)
finRaiseComm {zero} {zero} {Fin.zero} = refl
finRaiseComm {zero} {suc n} {Fin.zero} rewrite finRaiseComm {zero} {n} {Fin.zero} = refl
finRaiseComm {suc s} {zero} {Fin.zero} = refl
finRaiseComm {suc s} {zero} {Fin.suc x} = refl
finRaiseComm {suc s} {suc n} {Fin.zero} rewrite finRaiseComm {suc s} {n} {Fin.zero} = refl
finRaiseComm {suc s} {suc n} {Fin.suc x} rewrite finRaiseComm {suc s} {n} {Fin.suc x} = refl

raisePropCom : {n : ℕ} {t : Term s} -> raiseTermℕ (suc n) t ≡ raiseTermℕ n (raiseTerm t)
raisePropCom {.(suc _)} {zero} {Var x} = refl
raisePropCom {suc s} {suc n} {Var x} rewrite finRaiseComm {s} {n} {x} = refl

raisePropCom {s} {n} {App t1 t2}
  rewrite raisePropCom {s} {n} {t1} | raisePropCom {s} {n} {t2} = refl
raisePropCom {s} {n} {Abs t}
  rewrite raisePropCom {suc s} {n} {t} = refl
raisePropCom {s} {n} {unit} = refl
raisePropCom {s} {n} {Promote t}
  rewrite raisePropCom {s} {n} {t} = refl
raisePropCom {s} {n} {Let t1 t2}
  rewrite raisePropCom {s} {n} {t1}
        | raisePropCom {suc s} {n} {t2} = refl
raisePropCom {s} {n} {vtrue} = refl
raisePropCom {s} {n} {vfalse} = refl
raisePropCom {s} {n} {If t1 t2 t3}
  rewrite raisePropCom {s} {n} {t1}
        | raisePropCom {s} {n} {t2}
        | raisePropCom {s} {n} {t3} = refl
raisePropCom {s} {n} {tuple e1 e2}
    rewrite raisePropCom {s} {n} {e1}
          | raisePropCom {s} {n} {e2}
  = refl
raisePropCom {s} {n} {LetProd t1 t2}
    rewrite raisePropCom {s} {n} {t1}
          | raisePropCom {suc (suc s)} {n} {t2}
        = refl

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

  prodIntro : {s : ℕ}
              { Γ Γ1 Γ2 : Context s }
              { A B : Type }
              { t1 t2 : Term s }
           -> Γ1 ⊢ t1 ∶ A
           -> Γ2 ⊢ t2 ∶ B
           -> { res : Γ1 ++ Γ2 ≡ Γ }
           ------------------------------------
           -> Γ ⊢ tuple t1 t2 ∶ ProdTy A B

  prodElim : {s : ℕ}
             { Γ Γ1 Γ2 : Context s }
             { t1 : Term s }
             { t2 : Term (suc (suc s)) }
             { A B C : Type }
             { r : grade }
           -> Γ1 ⊢ t1 ∶ ProdTy A B
           -> Ext (Ext Γ2 (Grad A r)) (Grad B r) ⊢ t2 ∶ C
           ---------------------------------------------
           -> { res : ((r · Γ1) ++ Γ2) ≡ Γ }
           -> Γ ⊢ LetProd t1 t2 ∶ C

-- Value predicate
data Value : {s : ℕ} -> Term s -> Set where
  unitValue    : {s : ℕ} -> Value {s} unit
  varValue     : {s : ℕ} -> Value (Var (fromℕ s))
  absValue     : {s : ℕ} -> (t : Term (suc s)) -> Value (Abs t)
  promoteValue : {s : ℕ} -> (t : Term s) -> Value (Promote t)
  trueValue    : {s : ℕ} -> Value {s} vtrue
  falseValue   : {s : ℕ} -> Value {s} vfalse
  prodValue    : {s : ℕ} -> (t1 t2 : Term s) -> Value {s} t1 -> Value {s} t2 -> Value (tuple t1 t2)

postulate
  exchange : {{R : Semiring}}
             {s1 s2 : ℕ}
             {Γ1 : Context s1} {Γ2 : Context s2} {A B : Type} {r : grade}
             {t : Term (suc (s1 + s2))}
           -> (Ext Γ1 (Grad A r) ,, Γ2) ⊢ t ∶ B
           -> Ext (Γ1 ,, Γ2) (Grad A r) ⊢ t ∶ B
