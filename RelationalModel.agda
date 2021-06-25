{-# OPTIONS --allow-unsolved-metas #-}

module RelationalModel where

open import GrCore
open import Data.Unit hiding (_≤_; _≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool hiding (_≤_; _≟_)
open import Data.List hiding (_++_)
open import Data.Nat hiding (_≤_)
open import Function
open import Data.Maybe
open import Relation.Nullary

-- Based on Vineet and Deepak's paper model but without
-- heaps (as we don't have references) and without step indexing
-- (as we aren't considering recursion here).

-- # Unary interpretation of values in types
-- (as an indexed data type)

mutual

  {-# NO_POSITIVITY_CHECK #-}
  data [_]v : Type -> Term -> Set where
    unitInterpV : [ Unit ]v unit

    funInterpV  : {A B : Type} {r : Semiring}
               -> {x : ℕ}
               -> (e : Term)
               -> (forall (v : Term) ->
                    [ Box r A ]e (Promote v) -> [ B ]e (syntacticSubst v x e))

               -> [ FunTy A r B ]v (Abs x e)

    boxInterpV  : {A : Type} {r : Semiring}
               -> (e : Term)
               -> [ A ]e e -> [ Box r A ]v (Promote e)

    boolInterpTrue  : [ BoolTy ]v vtrue
    boolInterpFalse : [ BoolTy ]v vfalse

  -- # Unary interpretation of expressions in types

  [_]e : Type -> Term -> Set
  [ A ]e t =
    forall (v : Term)
    -> multiRedux t ≡ v -> [ A ]v v

-- # Relational interpretation of types

Rel : (A1 : Set) -> (A2 : Set) -> Set₁
Rel A1 A2 = A1 -> A2 -> Set

mutual
  -- # Binary interpretation of values in types

  {-# NO_POSITIVITY_CHECK #-}
  data ⟦_⟧v : Type ->  (Adv : Semiring) -> Rel Term Term where
    unitInterpE : {adv : Semiring} -> ⟦ Unit ⟧v adv unit unit

    funInterpE : {adv : Semiring} {A B : Type} {r : Semiring}
             -> {x y : ℕ}
             -> (e1 e2 : Term)
             -> (forall (v1 : Term) (v2 : Term)

               -- In the original model this:
               -- -> ⟦ A ⟧v adv {W} {_≤_} w' v1 v2
               -- But we have graded arrows here

                 -> ⟦ Box r A ⟧e adv (Promote v1) (Promote v2)
                 -> ⟦ B ⟧e adv (syntacticSubst v1 x e1) (syntacticSubst v2 y e2))
             ->   ⟦ FunTy A r B ⟧v adv (Abs x e1) (Abs y e2)

    -- Note:
    -- pre Hi Lo   false
    -- Lo ≤ Hi means adversary is lo, box is hi, so cannot observe the
    -- equality

    boxInterpEobs : {adv : Semiring} -> {A : Type} {r : Semiring}
              -> (r ≤ adv ≡ true)
              -> (t1 t2 : Term)
              -> ⟦ A ⟧e adv t1 t2
              -> ⟦ Box r A ⟧v adv (Promote t1) (Promote t2)

    boxInterpEunobs : {adv : Semiring} -> {A : Type} {r : Semiring}
              -> (r ≤ adv ≡ false)
              -> (t1 t2 : Term)
              -> ([ A ]e t1) × ([ A ]e t2)
              -> ⟦ Box r A ⟧v adv (Promote t1) (Promote t2)

    boxInterpTrueE  : {adv : Semiring} -> ⟦ BoolTy ⟧v adv vtrue vtrue
    boxInterpFalseE : {adv : Semiring} -> ⟦ BoolTy ⟧v adv vfalse vfalse

  {-# TERMINATING #-}
  -- # Binary interpretation of expressions in types
  ⟦_⟧e : Type -> (Adv : Semiring) -> Rel Term Term
  ⟦ tau ⟧e adv e1 e2 =
       forall (v1 v2 : Term)
    -> multiRedux e1 ≡ v1
    -> multiRedux e2 ≡ v2
    -> ⟦ tau ⟧v adv v1 v2

--------------
-- Contexts

-- unary
[_]Γ : {s : ℕ} -> Context s -> List Term -> Set
[ Empty            ]Γ _ = ⊤
[ Ext g (Grad A r) ]Γ (v ∷ vs) = ([ Box r A ]e (Promote v)) × ([ g ]Γ vs)
[ Ext _ _          ]Γ _ = ⊥

-- binary
⟦_⟧Γ : {s : ℕ} -> Context s -> (Adv : Semiring) -> List Term -> List Term -> Set
⟦ Empty   ⟧Γ adv _ _  = ⊤
⟦ Ext _ _ ⟧Γ adv _ [] = ⊥
⟦ Ext _ _ ⟧Γ adv [] _ = ⊥
⟦ Ext g (Grad A r) ⟧Γ adv (t1 ∷ ts1) (t2 ∷ ts2) =

   ⟦ Box r A ⟧e adv (Promote t1) (Promote t2)
   ×
   ⟦ g ⟧Γ adv ts1 ts2

-----------------------------

multisubst' : ℕ -> List Term -> Term -> Term
multisubst' n [] t' = t'
multisubst' n (t ∷ ts) t' =
  multisubst' (n + 1) ts (syntacticSubst t n t')

multisubst : List Term -> Term -> Term
multisubst ts t' = multisubst' 0 ts t'

-- Various preservation results about substitutions and values

substPresUnit : {γ : List Term} {n : ℕ} -> multisubst' n γ unit ≡ unit
substPresUnit {[]}    {n} = refl
substPresUnit {x ∷ g} {n} = substPresUnit {g} {n + 1}

substPresTrue : {γ : List Term} {n : ℕ} -> multisubst' n γ vtrue ≡ vtrue
substPresTrue {[]}    {n} = refl
substPresTrue {x ∷ g} {n} = substPresTrue {g} {n + 1}

substPresFalse : {γ : List Term} {n : ℕ} -> multisubst' n γ vfalse ≡ vfalse
substPresFalse {[]}    {n} = refl
substPresFalse {x ∷ g} {n} = substPresFalse {g} {n + 1}

substPresProm : {n : ℕ} {γ : List Term} {t : Term}
             -> multisubst' n γ (Promote t) ≡ Promote (multisubst' n γ t)
substPresProm {n} {[]} {t} = refl
substPresProm {n} {x ∷ γ} {t} = substPresProm {n + 1} {γ} {syntacticSubst x n t}

substPresAbs : {n : ℕ} {γ : List Term} {x : ℕ} {t : Term} -> multisubst' n γ (Abs x t) ≡ Abs x (multisubst' n γ t)
substPresAbs {n} {[]} {x} {t} = refl
substPresAbs {n} {v ∷ γ} {x} {t} with n ≟ x
... | yes refl = {!!}
... | no ¬p = substPresAbs {n + 1} {γ} {x} {syntacticSubst v n t}

reduxProm : {v : Term} -> multiRedux (Promote v) ≡ Promote v
reduxProm {v} = refl

postulate
 -- This is about the structure of substitutions and relates to abs
 -- there is some simplification here because of the definition of ,, being
 -- incorrect
  substitutionResult : {sz : ℕ} {v1' : Term} {γ1 : List Term} {t : Term} {Γ1 : Context sz}
   -> syntacticSubst v1' (Γlength Γ1 + 1) (multisubst' 0 γ1 t)
    ≡ multisubst (v1' ∷ γ1) t


-------------------------------

-- 0 · Γ

-- lemor : multisubst' 1 xs x ≡ v -> x ≡ v

-------------------------------

-------------------------------
-- Unary fundamental theorem

utheorem : {s : ℕ} {γ : List Term}
        -> {Γ : Context s} {e : Term} {τ : Type}
        -> Γ ⊢ e ∶ τ
        -> [ Γ ]Γ γ
        -> [ τ ]e (multisubst γ e)
utheorem {_} {γ} {Γ} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {_} {.Γ} {Γ1} {Γ2} pos) context v substi
 with γ | Γ | Γlength Γ1
... | x ∷ xs | Ext g (Grad A r) | zero = let z = subst (\h -> [ h ]v x) inja {!!} in {!!}
  where
    inja : A ≡ τ
    inja = injGradTy (injExt2 pos)


... | x ∷ a | Ext b x₁ | suc c = {!!}



utheorem {_} {γ} {Γ} {.(App _ _)} {τ} (app {_} {Γ} {Γ1} {Γ2} {r} typing typing₁) context = {!!}

utheorem {s} {γ} {Γ'} {Abs .(Γlength Γ1 + 1) t} {FunTy A r B} (abs {_} {_} {Γ} {Γ1} {Γ2} {Γ'} pos typing {rel}) context v substi rewrite pos | rel =
  subst (\h -> [ FunTy A r B ]v h) thm (funInterpV (multisubst γ t) body)
 where
   x = (Γlength Γ1 + 1)

   thm : Abs x (multisubst γ t) ≡ v
   thm =
     let
       qr = cong multiRedux (substPresAbs {0} {γ} {x} {t})
       qr' = trans qr (valuesDontReduce {Abs x (multisubst γ t)} (absValue {x} (multisubst γ t)))
     in sym (trans (sym substi) qr')

   body : (v' : Term) → [ Box r A ]e (Promote v') → [ B ]e (syntacticSubst v' x (multisubst γ t))
   body v' arg v1 prf =
     let
      ih = utheorem {{!!}} {v' ∷ γ}  {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} typing ( arg  , context)
     in {!!}


utheorem {s} {γ} {Γ'} {Promote t} {Box r A} (pr {_} {Γ} {Γ'} typing {prf}) context v substi rewrite prf =
   let
     ih = utheorem {{!!}} {γ} {Γ} {t} {A} typing (underBox context)
   in
     subst (\h -> [ Box r A ]v h) thm (boxInterpV (multisubst γ t) ih)
  where
    underBox : {sz : ℕ} {r : Semiring} {γ : List Term} {Γ : Context sz} -> [ r · Γ ]Γ γ -> [ Γ ]Γ γ
    underBox {0} {r} {_} {Empty}   g = tt
    underBox {sz} {r} {v ∷ γ} {Ext Γ (Grad A s)} (ass , g) = {!!} , underBox {{!!}} {r} {γ} {Γ} g
    underBox {_} {r} {_} {Ext Γ (Grad A r₁)} g = {!!}


    thm : Promote (multisubst γ t) ≡ v
    thm =
       let qr = cong multiRedux (substPresProm {0} {γ} {t})
           qr' = trans qr (valuesDontReduce {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym substi) qr')

utheorem {_} {γ} {.(Hi · _)} {.unit} {.Unit} unitConstr context v substi =
  subst (\h -> [ Unit ]v h) thm unitInterpV
  where
    thm : unit ≡ v
    thm = trans (sym (cong multiRedux (substPresUnit {γ} {0}))) substi

utheorem {_} {γ} {.(Hi · _)} {.vtrue} {.BoolTy} trueConstr context v substi =
 subst (\h -> [ BoolTy ]v h) thm boolInterpTrue
  where
    thm : vtrue ≡ v
    thm = trans (sym (cong multiRedux (substPresTrue {γ} {0}))) substi


utheorem {_} {γ} {.(Hi · _)} {.vfalse} {.BoolTy} falseConstr context v substi =
 subst (\h -> [ BoolTy ]v h) thm boolInterpFalse
  where
    thm : vfalse ≡ v
    thm = trans (sym (cong multiRedux (substPresFalse {γ} {0}))) substi

utheorem {_} {γ} {Γ} {.(If _ _ _)} {τ} (if typing typing₁ typing₂) context = {!!}

-------------------------------
-- Binary fundamental theorem

binaryImpliesUnaryV : {A : Type} {t1 t2 : Term} {adv : Semiring}
                  -> ⟦ A ⟧v adv t1 t2 -> [ A ]v t1 × [ A ]v t2
binaryImpliesUnaryV {FunTy A r A₁} {t1} {t2} {adv} arg = {!!}
binaryImpliesUnaryV {Unit} {.unit} {.unit} {adv} unitInterpE = unitInterpV , unitInterpV
binaryImpliesUnaryV {Box r A} {t1} {t2} {adv} arg = {!!}
binaryImpliesUnaryV {BoolTy} {t1} {t2} {adv} arg = {!!}

binaryImpliesUnary : {A : Type} {t1 t2 : Term} {adv : Semiring}
                  -> ⟦ A ⟧e adv t1 t2 -> [ A ]e t1 × [ A ]e t2
binaryImpliesUnary {FunTy A r A₁} {t1} {t2} {adv} arg = {!!}
binaryImpliesUnary {Unit} {t1} {t2} {adv} arg = (left , right)
  where
    left : [ Unit ]e t1
    left v redux with arg v v redux {!!}
    ... | unitInterpE = unitInterpV

    right : [ Unit ]e t2
    right v redux with arg v v {!!} {!!}
    ... | unitInterpE rewrite sym redux = {!!}

binaryImpliesUnary {Box r A} {t1} {t2} {adv} arg = {!!}
binaryImpliesUnary {BoolTy} {t1} {t2} {adv} arg = {!!}

biFundamentalTheorem : {sz : ℕ}
          {Γ : Context sz} {e : Term} {τ : Type}

        -> Γ ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : Semiring)
        -> ⟦ Γ ⟧Γ adv γ1 γ2
        -> ⟦ τ ⟧e adv (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheorem {_} {Γ} {.(Var (Γlength _))} {τ} (var pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}
biFundamentalTheorem {sz} {Γ} {App t1 t2} {τ} (app {s} {Γ} {Γ1} {Γ2} {r} {A} {B} typ1 typ2 {pos}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
   let
    ih1 = biFundamentalTheorem {{!!}} {Γ1} {t1} {FunTy A r B} typ1 adv {!!} {!!} {!!} {!!} {!!}
    ih2 = biFundamentalTheorem {{!!}} {Γ2} {t2} {A} typ2 adv {!!} {!!} {!!} {!!} {!!}
   in
     {!!}
  where
    splitContext1 : {sz : ℕ} {γ1 γ2 : List Term} {Γ1 Γ2 : Context sz} -> ⟦ Γ1 ++ (r · Γ2) ⟧Γ adv γ1 γ2 -> ⟦ Γ1 ⟧Γ adv γ1 γ2
    splitContext1 {0} {γ1} {γ2} {Empty} {Empty} g = tt
    splitContext1 {sz} {γ1} {γ2} {Ext Γ1 x} {Ext Γ2 x₁} g = {!!}

biFundamentalTheorem {sz} {Γ'} {Abs .(Γlength Γ1 + 1) t} {FunTy A r B} (abs {s1} {s2} {Γ} {Γ1} {Γ2} {Γ'} pos typ {rel}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ FunTy A r B ⟧v adv h1 h2) (thm γ1 v1 v1redux) (thm γ2 v2 v2redux) (funInterpE {adv} {A} {B} {r} {Γlength Γ1 + 1} {Γlength Γ1 + 1} (multisubst γ1 t) ((multisubst γ2 t)) body)
  where
    body : (forall (v1' : Term) (v2' : Term)
         -> ⟦ Box r A ⟧e adv (Promote v1') (Promote v2')
         -> ⟦ B ⟧e adv (syntacticSubst v1' (Γlength Γ1 + 1) (multisubst γ1 t)) (syntacticSubst v2' (Γlength Γ1 + 1) (multisubst γ2 t)))
    body v1' v2' arg rewrite pos | rel | (substitutionResult {{!!}} {v1'} {γ1} {t} {Γ1}) | (substitutionResult {{!!}} {v2'} {γ2} {t} {Γ1}) =
      biFundamentalTheorem {{!!}} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} typ {v1' ∷ γ1} {v2' ∷ γ2} adv (arg , contextInterp)

    thm : (γ : List Term) -> (v : Term)
        -> multiRedux (multisubst γ (Abs (Γlength Γ1 + 1) t)) ≡ v -> Abs (Γlength Γ1 + 1) (multisubst γ t) ≡ v
    thm γ v redux =
     let
       qr = cong multiRedux (substPresAbs {0} {γ} {Γlength Γ1 + 1} {t})
       qr' = trans qr (valuesDontReduce {Abs (Γlength Γ1 + 1) (multisubst γ t)} (absValue {Γlength Γ1 + 1} (multisubst γ t)))
     in sym (trans (sym redux) qr')


biFundamentalTheorem {sz} {Γ'} {Promote t} {Box r A} (pr {s} {Γ} {Γ'} typ {prf}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux with r ≤ adv | inspect (\x -> x ≤ adv) r
... | false | [ eq ] rewrite prf =
  let
    (uinterp1 , uinterp2) = underBox {{!!}} {γ1} {γ2} {Γ} contextInterp
    ih1 = utheorem {{!!}} {γ1} {Γ} {t} {A} typ uinterp1
    ih2 = utheorem {{!!}} {γ2} {Γ} {t} {A} typ uinterp2
  in
   subst₂ (\h1 h2 -> ⟦ Box r A ⟧v adv h1 h2) (thm {v1} {γ1} v1redux) (thm {v2} {γ2} v2redux)
             (boxInterpEunobs eq (multisubst γ1 t) (multisubst γ2 t) (ih1 , ih2))
  where
    thm : {v : Term} {γ : List Term} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
    thm {v} {γ} redux =
       let qr = cong multiRedux (substPresProm {0} {γ} {t})
           qr' = trans qr (valuesDontReduce {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')

    binaryToUnaryVal : {s : Semiring} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ([ Box s A ]v (Promote v1)) × ([ Box s A ]v (Promote v2))
    binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpEobs eq' .v1 .v2 ainterp) =
      ⊥-elim bot
       where
        bot : ⊥
        bot with (trans (sym eq') (invPropertyD eq))
        ... | ()

    binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpEunobs eq .v1 .v2 (left , right)) = (boxInterpV v1 left) , (boxInterpV v2 right)

    binaryToUnaryExp : {s : Semiring} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ([ Box s A ]e (Promote v1)) × ([ Box s A ]e (Promote v2))
    binaryToUnaryExp {s} {v1} {v2} {A} arg1 = (left , right)
      where
        left : [ Box s A ]e (Promote v1)
        left v0 redux rewrite trans (sym redux) (reduxProm {v1}) with binaryToUnaryVal {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
        ... | (left' , right') = left'

        right : [ Box s A ]e (Promote v2)
        right v0 redux rewrite trans (sym redux) (reduxProm {v2}) with binaryToUnaryVal {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
        ... | (left' , right') = right'

    underBox : {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> [ Γ ]Γ γ1 × [ Γ ]Γ γ2
    underBox {_} {_} {_} {Empty} g = (tt , tt)
    underBox {_} {[]} {[]} {Ext Γ (Grad A r)} ()
    underBox {_} {[]} {x ∷ γ2} {Ext Γ (Grad A r)} ()
    underBox {_} {x ∷ γ1} {[]} {Ext Γ (Grad A r)} ()
    underBox {sz} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A r')} (arg , g) =
     let
      (left , right) = underBox {{!!}} {γ1} {γ2} {Γ} g
      (l , r) = binaryToUnaryExp arg
     in
       (l , left) , (r , right)

--------------------------------------------------------
... | true  | [ eq ] rewrite prf =
  let
    ih = biFundamentalTheorem {{!!}} {Γ} {t} {A} typ {γ1} {γ2} adv (underBox {{!!}} {γ1} {γ2} contextInterp)
  in
    subst₂ (\h1 h2 -> ⟦ Box r A ⟧v adv h1 h2) (thm {v1} {γ1} v1redux) (thm {v2} {γ2} v2redux) (boxInterpEobs eq (multisubst γ1 t) (multisubst γ2 t) ih)

  where

    thing2 : {s : Semiring} {v1 : Term} {v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧v adv (Promote v1) (Promote v2)
    thing2 {s} {v1} {v2} {A} (boxInterpEobs prop .v1 .v2 interp) = boxInterpEobs prop' v1 v2 interp
       where
        prop' : (s ≤ adv) ≡ true
        prop' = invPropertyA prop

    thing2 {s} {v1} {v2} {A} (boxInterpEunobs x .v1 .v2 interp) = boxInterpEunobs (invPropertyC x eq) v1 v2 interp

    thing : {s : Semiring} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧e adv (Promote v1) (Promote v2)
    thing {s} {v1} {v2} {A} arg1 v1' v2' v1redux' v2redux' rewrite trans (sym v1redux') (reduxProm {v1}) | trans (sym v2redux') (reduxProm {v2}) =
       thing2  {s} {v1} {v2} {A} (arg1 (Promote v1) (Promote v2) refl refl)

    underBox : {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> ⟦ Γ ⟧Γ adv γ1 γ2
    underBox {_} {_} {_} {Empty}   g = tt
    underBox {sz} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A s)} (ass , g) = thing {s} {v1} {v2} {A} ass , underBox {{!!}} {γ1} {γ2} {Γ} g
    underBox {_} {[]} {[]} {Ext Γ (Grad A r₁)} ()
    underBox {_} {[]} {x ∷ γ5} {Ext Γ (Grad A r₁)} ()
    underBox {_} {x ∷ γ4} {[]} {Ext Γ (Grad A r₁)} ()

    thm : {v : Term} {γ : List Term} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
    thm {v} {γ} redux =
       let qr = cong multiRedux (substPresProm {0} {γ} {t})
           qr' = trans qr (valuesDontReduce {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')


biFundamentalTheorem {_} {.(Hi · _)} {.unit} {.Unit} unitConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ Unit ⟧v adv h1 h2) thm1 thm2 (unitInterpE {adv})
    where
      thm1 : unit ≡ v1
      thm1 = trans (sym (cong multiRedux (substPresUnit {γ1} {0}))) v1redux

      thm2 : unit ≡ v2
      thm2 = trans (sym (cong multiRedux (substPresUnit {γ2} {0}))) v2redux


biFundamentalTheorem {_} {.(Hi · _)} {.vtrue} {.BoolTy} trueConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ BoolTy ⟧v adv h1 h2) thm1 thm2 boxInterpTrueE
   where
    thm1 : vtrue ≡ v1
    thm1 = trans (sym (cong multiRedux (substPresTrue {γ1} {0}))) v1redux

    thm2 : vtrue ≡ v2
    thm2 = trans (sym (cong multiRedux (substPresTrue {γ2} {0}))) v2redux

biFundamentalTheorem {_} {.(Hi · _)} {.vfalse} {.BoolTy} falseConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ BoolTy ⟧v adv h1 h2) thm1 thm2 boxInterpFalseE
   where
    thm1 : vfalse ≡ v1
    thm1 = trans (sym (cong multiRedux (substPresFalse {γ1} {0}))) v1redux

    thm2 : vfalse ≡ v2
    thm2 = trans (sym (cong multiRedux (substPresFalse {γ2} {0}))) v2redux

biFundamentalTheorem {_} {.(_ GrCore.++ _)} {.(If _ _ _)} {τ} (if typ typ₁ typ₂) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

lem : {adv : Semiring}
      {A : Type} {v1 v2 : Term}
   -> Value v1
   -> Value v2
   -> ⟦ A ⟧e adv v1 v2
   -> ⟦ A ⟧v adv v1 v2

lem {adv} {A} {v1} {v2} isvalv1 isvalv2 mem =
  mem v1 v2 (valuesDontReduce {v1} isvalv1) (valuesDontReduce {v2} isvalv2)


boolBinaryValueInterpEquality : (v1 v2 : Term) -> ⟦ BoolTy ⟧v Lo v1 v2 -> v1 ≡ v2
boolBinaryValueInterpEquality .vtrue .vtrue boxInterpTrueE = refl
boolBinaryValueInterpEquality .vfalse .vfalse boxInterpFalseE = refl

boolBinaryExprInterpEquality : (v1 v2 : Term)
                              -> ⟦ BoolTy ⟧e Lo v1 v2
                              -> multiRedux v1 ≡ multiRedux v2
boolBinaryExprInterpEquality t1 t2 prf =
  boolBinaryValueInterpEquality (multiRedux t1) (multiRedux t2) ((prf (multiRedux t1) (multiRedux t2) refl refl))
--

-- Value lemma for promotion
promoteValueLemma : {v : Term} {r : Semiring} {A : Type}

  -> Empty ⊢ v ∶ Box r A
  -> Value v
  -> Σ Term (\v' -> v ≡ Promote v')

promoteValueLemma {_} {r} () varValue

promoteValueLemma typing (promoteValue t) = t , refl


-- Non-interference
nonInterfSpecialised : {A : Type} {e : Term}
        -> Ext Empty (Grad A Hi) ⊢ e ∶ Box Lo BoolTy

        -> (v1 v2 : Term)
        -> Empty ⊢ v1 ∶ A
        -> Empty ⊢ v2 ∶ A
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) == multiRedux (syntacticSubst v2 0 e)

nonInterfSpecialised {A} {e} typing v1 v2 v1typing v2typing isvalv1 isvalv2 with
    -- Apply fundamental binary theorem to v1
    biFundamentalTheorem {zero} {Empty} {Promote v1} {Box Hi A}
                  (pr v1typing {refl}) {[]} {[]} Lo tt (Promote v1) (Promote v1)
                  (valuesDontReduce {Promote v1} (promoteValue v1))
                  (valuesDontReduce {Promote v1} (promoteValue v1))
    -- Apply fundamental binary theorem to v2
  | biFundamentalTheorem {zero} {Empty} {Promote v2} {Box Hi A}
                  (pr v2typing {refl})  {[]} {[]} Lo tt (Promote v2) (Promote v2)
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  (valuesDontReduce {Promote v2} (promoteValue v2))
... | boxInterpEunobs refl .v1 .v1 (valv1 , valv1') | boxInterpEunobs refl .v2 .v2 (valv2 , valv2') =
 let
   -- Show that substituting v1 and evaluating yields a value
   -- and since it is a graded modal type then this value is necessarily
   -- of the form Promote v1''
   substTy1 = substitution {zero} {zero} {Ext Empty (Grad A Hi)} {Empty} {Empty} {Empty} {Hi} typing refl v1typing
   (v1'' , prf1) = promoteValueLemma {_} {Lo} {BoolTy} (preservation {zero} {Empty} {Box Lo BoolTy} {syntacticSubst v1 0 e} substTy1) (multiReduxProducesValues substTy1)

   -- ... same as above but for v2 ... leading to result of Promote v2''
   substTy2  = substitution {zero} {zero} {Ext Empty (Grad A Hi)} {Empty} {Empty} {Empty} {Hi} typing refl v2typing
   (v2'' , prf2) = promoteValueLemma {_} {Lo} {BoolTy} (preservation {zero} substTy2) (multiReduxProducesValues substTy2)

   -- Apply fundamental binary theorem on the result with the values coming from syntacitcally substituting
   -- then evaluating
   res = biFundamentalTheorem {1} {Ext Empty (Grad A Hi)} {e} {Box Lo BoolTy} typing {v1 ∷ []} {v2 ∷ []} Lo
          (inner valv1' valv2' , tt) (Promote v1'') (Promote v2'') prf1 prf2


   -- Boolean typed (low) values are equal inside the binary interepration
   boolTyEq = boolBinaryExprInterpEquality v1'' v2'' (unpack res)

   -- Plug together the equalities
     -- Promote
   eq = PromoteEq {v1''} {v2''} (embedReduxCong {v1''} {v2''} boolTyEq)
   eq2 = transFullBetaEq (embedEq prf1) eq

 in transFullBetaEq eq2 (embedEq (sym prf2))
   where

     inner : [ A ]e v1 -> [ A ]e v2 -> ⟦ Box Hi A ⟧e Lo (Promote v1) (Promote v2)
     inner av1 av2 v3 v4 v3redux v4redux
       rewrite trans (sym v3redux) (valuesDontReduce {Promote v1} (promoteValue v1))
             | trans (sym v4redux) (valuesDontReduce {Promote v2} (promoteValue v2)) =
       boxInterpEunobs refl v1 v2 (av1 , av2)

     -- Helper to unpback interpretation type
     unpack : {v1 v2 : Term} -> ⟦ Box Lo BoolTy ⟧v Lo (Promote v1) (Promote v2) -> ⟦ BoolTy ⟧e Lo v1 v2
     unpack {v1} {v2} (boxInterpEobs _ .v1 .v2 innerExprInterp) = innerExprInterp

{-
nonInterf : {A : Type} {li l : Semiring} {e : Term}
        -> (li ≤ l ≡ false)  -- condition on labels
        -> Ext Empty (Grad A li) ⊢ e ∶ Box l BoolTy

        -> (v1 v2 : Term)
        -> Empty ⊢ v1 ∶ A
        -> Empty ⊢ v2 ∶ A
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) ≡ multiRedux (syntacticSubst v2 0 e)

nonInterf {A} {li} {l} {e} rel typing v1 v2 v1typing v2typing isvalv1 isvalv2 =
  let
       ev1 = biFundamentalTheorem {Empty} {Promote v1} {Box li A}
                  (pr v1typing) {[]} {[]} l tt

      -- uth1 = utheorem {Semiring} {ord} {{!!}} {[]} {Empty} {v1} {A} v1typing {{!!}} tt
      -- uth2 = utheorem {Semiring} {ord} {{!!}} {[]} {Empty} {v2} {A} v2typing {{!!}} tt

      -- fromUtoV = ulem {Semiring} {ord} {{!!}} {{!!}} {{!!}} {{!!}} (uth1 {!!} {!!}) {!!}

      -- (l' , (rel , ev1')) = lem {Semiring} {ord} {li} {l} {Box li A}
      --     {Promote v1} {Promote v1} (promoteValue isvalv1) (promoteValue isvalv1) ev1

       x = biFundamentalTheorem {Ext Empty (Grad A li)} {e}
              {Box l BoolTy} typing {v1 ∷ []} {v2 ∷ []} l ({!!} , tt)
  in {!!}
-}
