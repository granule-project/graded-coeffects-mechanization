{-# OPTIONS --allow-unsolved-metas #-}

module RelationalModel where

open import GrCore
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool hiding (_≤_)
open import Data.List
open import Data.Nat hiding (_≤_)
open import Function
open import Data.Maybe

-- Based on Vineet and Deepak's paper model but without
-- heaps (as we don't have references) and without step indexing
-- (as we aren't considering recursion here).

-- # Helpers
unequalContexts : {G G' : Context} {A : Assumption} -> Empty ≡ Ext G A ,, G' -> ⊥
unequalContexts {Empty} {Empty} {A} ()
unequalContexts {Empty} {Ext G' x} {A} ()
unequalContexts {Ext G x} {Empty} {A} ()
unequalContexts {Ext G x} {Ext G' x₁} {A} ()

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

  {-# TERMINATING #-}
  ⟦_⟧v : Type ->  (Adv : Semiring) -> Rel Term Term
  ⟦ Unit ⟧v adv unit unit = ⊤

  ⟦ FunTy A r B ⟧v adv (Abs x e1) (Abs y e2) =
    (forall (v1 : Term) (v2 : Term)

   -- In the original model this:
   -- -> ⟦ A ⟧v adv {W} {_≤_} w' v1 v2
   -- But we have graded arrows here

    -> ⟦ Box r A ⟧e adv (Promote v1) (Promote v2)
    -> ⟦ B ⟧e adv (syntacticSubst v1 x e1) (syntacticSubst v2 y e2))

  -- Note:
  -- pre Hi Lo   false
  -- Lo ≤ Hi means adversary is lo, box is hi, so cannot observe the
  -- equality

  ⟦ Box r A ⟧v adv (Promote t1) (Promote t2) with r ≤ adv
  ... | true  = ⟦ A ⟧e adv t1 t2
  ... | false = ([ A ]e t1) × ([ A ]e t2)

  ⟦ BoolTy ⟧v adv vtrue vtrue = ⊤

  ⟦ BoolTy ⟧v adv vfalse vfalse = ⊤

  ⟦ _ ⟧v adv _ _ = ⊥

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
[_]Γ : Context -> List Term -> Set
[ Empty            ]Γ _ = ⊤
[ Ext _ _          ]Γ [] = ⊥
[ Ext g (Grad A r) ]Γ (v ∷ vs) =
  ([ A ]e v) × ([ g ]Γ vs)

-- binary
⟦_⟧Γ : Context -> (Adv : Semiring) -> List Term -> List Term -> Set
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

-------------------------------

-- 0 · Γ

-- lemor : multisubst' 1 xs x ≡ v -> x ≡ v

-------------------------------

-------------------------------
-- Unary fundamental theorem

utheorem : {γ : List Term}
        -> {Γ : Context} {e : Term} {τ : Type}
        -> Γ ⊢ e ∶ τ
        -> [ Γ ]Γ γ
        -> [ τ ]e (multisubst γ e)
utheorem {γ} {Γ} {.(Var (Γlength Γ1))} {τ} (var {_} {.Γ} {Γ1} {Γ2} pos) context v substi
 with γ | Γ | Γlength Γ1
... | _ | Empty | _ = ⊥-elim (unequalContexts {Hi · Γ1} {Hi · Γ2} {Grad τ Lo} pos)
... | x ∷ xs | Ext g (Grad A r) | zero = let z = subst (\h -> [ h ]v x) inja {!!} in {!!}
  where
    inja : A ≡ τ
    inja = injGradTy (injExt2 pos)


... | x ∷ a | Ext b x₁ | suc c = {!!}

{- ... | [] | Empty = ⊥-elim (unequalContexts {Hi · Γ1} {Hi · Γ2} {Grad τ Lo} pos)
... | x ∷ x₁ | Empty = ⊥-elim (unequalContexts pos)
... | x ∷ xs | Ext y g with 0 Data.Nat.≟ GrCore.length Γ1
-}

utheorem {γ} {Γ} {.(App _ _)} {τ} (app {Γ} {Γ1} {Γ2} {r} typing typing₁) context = {!!}
utheorem {γ} {Γ} {.(Abs (Γlength _ + 1) _)} {.(FunTy _ _ _)} (abs pos typing) context = {!!}


utheorem {γ} {Γ'} {Promote t} {Box r A} (pr {Γ} {Γ'} typing {prf}) context v substi rewrite prf =
   let
     ih = utheorem {γ} {Γ} {t} {A} typing (underBox context)
   in
     subst (\h -> [ Box r A ]v h) thm (boxInterpV (multisubst γ t) ih)
  where
    underBox : {r : Semiring} {γ : List Term} {Γ : Context} -> [ r · Γ ]Γ γ -> [ Γ ]Γ γ
    underBox {r} {_} {Empty}   g = tt
    underBox {r} {[]} {Ext Γ x} g with r · (Ext Γ x)
    ... | Empty = {!!}
    underBox {r} {x₁ ∷ γ} {Ext Γ x} g = {!!}

    lem : {n : ℕ} {γ : List Term} {t : Term} -> multisubst' n γ (Promote t) ≡ Promote (multisubst' n γ t)
    lem {n} {[]} {t} = refl
    lem {n} {x ∷ γ} {t} = lem {n + 1} {γ} {syntacticSubst x n t}

    mr : {t : Term} -> multiRedux (Promote t) ≡ Promote t
    mr {t} = refl

    thm : Promote (multisubst γ t) ≡ v
    thm =
       let (rel) = lem {0} {γ} {t}
           qr = cong multiRedux rel
           qr' = trans qr (mr {(multisubst γ t)})
       in sym (trans (sym substi) qr')

utheorem {γ} {.(Hi · _)} {.unit} {.Unit} unitConstr context v substi =
  subst (\h -> [ Unit ]v h) thm unitInterpV

  where
    lem : {γ : List Term} {n : ℕ} -> multisubst' n γ unit ≡ unit
    lem {[]}    {n} = refl
    lem {x ∷ g} {n} = lem {g} {n + 1}

    thm : unit ≡ v
    thm = trans (sym (cong multiRedux (lem {γ} {0}))) substi

utheorem {γ} {.(Hi · _)} {.vtrue} {.BoolTy} trueConstr context v substi =
 subst (\h -> [ BoolTy ]v h) thm boolInterpTrue

  where
    lem : {γ : List Term} {n : ℕ} -> multisubst' n γ vtrue ≡ vtrue
    lem {[]}    {n} = refl
    lem {x ∷ g} {n} = lem {g} {n + 1}

    thm : vtrue ≡ v
    thm = trans (sym (cong multiRedux (lem {γ} {0}))) substi


utheorem {γ} {.(Hi · _)} {.vfalse} {.BoolTy} falseConstr context v substi =
 subst (\h -> [ BoolTy ]v h) thm boolInterpFalse

  where
    lem : {γ : List Term} {n : ℕ} -> multisubst' n γ vfalse ≡ vfalse
    lem {[]}    {n} = refl
    lem {x ∷ g} {n} = lem {g} {n + 1}

    thm : vfalse ≡ v
    thm = trans (sym (cong multiRedux (lem {γ} {0}))) substi

utheorem {γ} {Γ} {.(If _ _ _)} {τ} (if typing typing₁ typing₂) context = {!!}

-------------------------------
-- Binary fundamental theorem

biFundamentalTheorem :
          {Γ : Context} {e : Term} {τ : Type}

        -> Γ ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : Semiring)
        -> ⟦ Γ ⟧Γ adv γ1 γ2
        -> ⟦ τ ⟧e adv (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheorem {Γ} {.(Var (Γlength _))} {τ} (var pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}
biFundamentalTheorem {Γ} {.(App _ _)} {τ} (app typ typ₁) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}
biFundamentalTheorem {Γ} {.(Abs (Γlength _ + 1) _)} {.(FunTy _ _ _)} (abs pos typ) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}
biFundamentalTheorem {Γ} {.(Promote _)} {.(Box _ _)} (pr typ) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

biFundamentalTheorem {.(Hi · _)} {.unit} {.Unit} unitConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

biFundamentalTheorem {.(Hi · _)} {.vtrue} {.BoolTy} trueConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}
biFundamentalTheorem {.(Hi · _)} {.vfalse} {.BoolTy} falseConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}
biFundamentalTheorem {.(_ GrCore.++ _)} {.(If _ _ _)} {τ} (if typ typ₁ typ₂) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

lem : {adv : Semiring}
      {A : Type} {v1 v2 : Term}
   -> Value v1
   -> Value v2
   -> ⟦ A ⟧e adv v1 v2
   -> ⟦ A ⟧v adv v1 v2

lem {adv} {A} {v1} {v2} isvalv1 isvalv2 mem =
  mem v1 v2 (valuesDontReduce {v1} isvalv1) (valuesDontReduce {v2} isvalv2)


boolBinaryValueInterpEquality : (v1 v2 : Term) -> ⟦ BoolTy ⟧v Lo v1 v2 -> v1 ≡ v2
boolBinaryValueInterpEquality (Var x) (Var x₁) ()
boolBinaryValueInterpEquality (Var x) (App v2 v3) ()
boolBinaryValueInterpEquality (Var x) (Abs x₁ v2) ()
boolBinaryValueInterpEquality (Var x) unit ()
boolBinaryValueInterpEquality (Var x) (Promote v2) ()
boolBinaryValueInterpEquality (Var x) vtrue ()
boolBinaryValueInterpEquality (Var x) vfalse ()
boolBinaryValueInterpEquality (Var x) (If v2 v3 v4) ()
boolBinaryValueInterpEquality (App v1 v2) (Var x) ()
boolBinaryValueInterpEquality (App v1 v2) (App v3 v4) ()
boolBinaryValueInterpEquality (App v1 v2) (Abs x v3) ()
boolBinaryValueInterpEquality (App v1 v2) unit ()
boolBinaryValueInterpEquality (App v1 v2) (Promote v3) ()
boolBinaryValueInterpEquality (App v1 v2) vtrue ()
boolBinaryValueInterpEquality (App v1 v2) vfalse ()
boolBinaryValueInterpEquality (App v1 v2) (If v3 v4 v5) ()
boolBinaryValueInterpEquality (Abs x v1) (Var x₁) ()
boolBinaryValueInterpEquality (Abs x v1) (App v2 v3) ()
boolBinaryValueInterpEquality (Abs x v1) (Abs x₁ v2) ()
boolBinaryValueInterpEquality (Abs x v1) unit ()
boolBinaryValueInterpEquality (Abs x v1) (Promote v2) ()
boolBinaryValueInterpEquality (Abs x v1) vtrue ()
boolBinaryValueInterpEquality (Abs x v1) vfalse ()
boolBinaryValueInterpEquality (Abs x v1) (If v2 v3 v4) ()
boolBinaryValueInterpEquality unit (Var x) ()
boolBinaryValueInterpEquality unit (App v2 v3) ()
boolBinaryValueInterpEquality unit (Abs x v2) ()
boolBinaryValueInterpEquality unit unit ()
boolBinaryValueInterpEquality unit (Promote v2) ()
boolBinaryValueInterpEquality unit vtrue ()
boolBinaryValueInterpEquality unit vfalse ()
boolBinaryValueInterpEquality unit (If v2 v3 v4) ()
boolBinaryValueInterpEquality (Promote v1) (Var x) ()
boolBinaryValueInterpEquality (Promote v1) (App v2 v3) ()
boolBinaryValueInterpEquality (Promote v1) (Abs x v2) ()
boolBinaryValueInterpEquality (Promote v1) unit ()
boolBinaryValueInterpEquality (Promote v1) (Promote v2) ()
boolBinaryValueInterpEquality (Promote v1) vtrue ()
boolBinaryValueInterpEquality (Promote v1) vfalse ()
boolBinaryValueInterpEquality (Promote v1) (If v2 v3 v4) ()
boolBinaryValueInterpEquality vtrue (Var x) ()
boolBinaryValueInterpEquality vtrue (App v2 v3) ()
boolBinaryValueInterpEquality vtrue (Abs x v2) ()
boolBinaryValueInterpEquality vtrue unit ()
boolBinaryValueInterpEquality vtrue (Promote v2) ()
boolBinaryValueInterpEquality vtrue vtrue tt = refl
boolBinaryValueInterpEquality vtrue vfalse ()
boolBinaryValueInterpEquality vtrue (If v2 v3 v4) ()
boolBinaryValueInterpEquality vfalse (Var x) ()
boolBinaryValueInterpEquality vfalse (App v2 v3) ()
boolBinaryValueInterpEquality vfalse (Abs x v2) ()
boolBinaryValueInterpEquality vfalse unit ()
boolBinaryValueInterpEquality vfalse (Promote v2) ()
boolBinaryValueInterpEquality vfalse vtrue ()
boolBinaryValueInterpEquality vfalse vfalse tt = refl
boolBinaryValueInterpEquality vfalse (If v2 v3 v4) ()
boolBinaryValueInterpEquality (If v1 v2 v3) (Var x) ()
boolBinaryValueInterpEquality (If v1 v2 v3) (App v4 v5) ()
boolBinaryValueInterpEquality (If v1 v2 v3) (Abs x v4) ()
boolBinaryValueInterpEquality (If v1 v2 v3) unit ()
boolBinaryValueInterpEquality (If v1 v2 v3) (Promote v4) ()
boolBinaryValueInterpEquality (If v1 v2 v3) vtrue ()
boolBinaryValueInterpEquality (If v1 v2 v3) vfalse ()
boolBinaryValueInterpEquality (If v1 v2 v3) (If v4 v5 v6) ()

boolBinaryExprInterpEquality : (v1 v2 : Term)
                              -> ⟦ BoolTy ⟧e Lo v1 v2
                              -> multiRedux v1 ≡ multiRedux v2
boolBinaryExprInterpEquality t1 t2 prf = boolBinaryValueInterpEquality (multiRedux t1) (multiRedux t2) ((prf (multiRedux t1) (multiRedux t2) refl refl))
--

-- Value lemma for promotion
promoteValueLemma : {v : Term} {r : Semiring} {A : Type}

  -> Empty ⊢ v ∶ Box r A
  -> Value v
  -> Σ Term (\v' -> v ≡ Promote v')

promoteValueLemma {_} {r} (var {A} {.Empty} {Γ1} {Γ2} pos) varValue =
  ⊥-elim (unequalContexts {Hi · Γ1} {Hi · Γ2} {Grad A Lo} pos)

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

nonInterfSpecialised {A} {e} typing v1 v2 v1typing v2typing isvalv1 isvalv2 =
 let
   -- Apply fundamental binary theorem to v1
   (valv1 , valv1') = biFundamentalTheorem {Empty} {Promote v1} {Box Hi A}
                  (pr v1typing {refl}) {[]} {[]} Lo tt (Promote v1) (Promote v1)
                  (valuesDontReduce {Promote v1} (promoteValue v1))
                  (valuesDontReduce {Promote v1} (promoteValue v1))

   -- Apply fundamental binary theorem to v2
   (valv2 , valv2') = biFundamentalTheorem {Empty} {Promote v2} {Box Hi A}
                  (pr v2typing {refl})  {[]} {[]} Lo tt (Promote v2) (Promote v2)
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  (valuesDontReduce {Promote v2} (promoteValue v2))

   -- Show that substituting v1 and evaluating yields a value
   -- and since it is a graded modal type then this value is necessarily
   -- of the form Promote v1''
   substTy1 = substitution {Ext Empty (Grad A Hi)} {Empty} {Empty} {Empty} {Hi} typing refl v1typing
   (v1'' , prf1) = promoteValueLemma {_} {Lo} {BoolTy} (preservation {Empty} {Box Lo BoolTy} {syntacticSubst v1 0 e} substTy1) (multiReduxProducesValues substTy1)

   -- ... same as above but for v2 ... leading to result of Promote v2''
   substTy2  = substitution {Ext Empty (Grad A Hi)} {Empty} {Empty} {Empty} {Hi} typing refl v2typing
   (v2'' , prf2) = promoteValueLemma {_} {Lo} {BoolTy} (preservation substTy2) (multiReduxProducesValues substTy2)

   -- Apply fundamental binary theorem on the result with the values coming from syntacitcally substituting
   -- then evaluating
   res = biFundamentalTheorem {Ext Empty (Grad A Hi)} {e} {Box Lo BoolTy} typing {v1 ∷ []} {v2 ∷ []} Lo
          (inner valv1' valv2' , tt) (Promote v1'') (Promote v2'') prf1 prf2

   -- Boolean typed (low) values are equal inside the binary interepration
   boolTyEq = boolBinaryExprInterpEquality v1'' v2'' res

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
       (av1 , av2)


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
