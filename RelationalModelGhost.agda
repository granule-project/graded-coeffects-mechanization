{-# OPTIONS --allow-unsolved-metas #-}

module RelationalModelGhost where

open import GrCore hiding (_⊢_∶_)
open import GrCoreGhost

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
open import Data.Sum

open import Semiring

-- open Semiring.Semiring {{...}} public
open NonInterferingSemiring {{...}} public

open import RelationalModel

data InfoContext {{ R : Semiring }} : (r : grade) -> Set where
  Visible :   {r adv : grade}  -> r ≤ adv -> InfoContext r
  Invisible : {r adv : grade}  -> adv ≤ r -> InfoContext r

-- Contexts

-- unary
[_]Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> List Term -> Set
[ (Γ , ghostGrade) ]Γg γ = [ Γ ]Γ γ × InfoContext ghostGrade

-- binary
⟦_⟧Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> (adv : grade) -> List Term -> List Term -> Set
⟦ (Γ , ghostGrade)   ⟧Γg adv γ1 γ2 = ⟦ Γ ⟧Γ adv γ1 γ2 × InfoContext ghostGrade

injPair1 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> a ≡ a'
injPair1 refl = refl

injPair2 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> b ≡ b'
injPair2 refl = refl

binaryImpliesUnaryGg : {{R : Semiring}} {sz : ℕ} { Γ : Context sz } {adv : grade} {γ1 γ2 : List Term}
                    -> ⟦ Γ ⟧Γ adv γ1 γ2 -> ([ Γ ]Γ γ1) × ([ Γ ]Γ γ2)
binaryImpliesUnaryGg {.0} {Empty} {adv} {_} {_} pre = tt , tt
binaryImpliesUnaryGg {suc sz} {Ext Γ (Grad A r)} {adv} {v1 ∷ γ1} {v2 ∷ γ2} (arg , rest)
  with binaryImpliesUnary {Box r A} {Promote v1} {Promote v2} {adv} arg | binaryImpliesUnaryG {sz} {Γ} {adv} {γ1} {γ2} rest
... | ( arg1 , arg2 ) | ( rest1 , rest2 ) = ( (arg1 , rest1) , (arg2 , rest2) )

promoteLemma : {t t' t'' : Term} -> Promote t ≡ t' -> Σ Term (\t'' -> Promote t'' ≡ t')
promoteLemma {t} {t'} {t''} pre = {!!}

{-# TERMINATING #-}
biFundamentalTheoremGhost : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2
        -> ⟦ Box ghost τ ⟧e adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))

biFundamentalTheoremGhost {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux
 rewrite injPair1 pos | sym (injPair2 pos) | sym v1redux | sym v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as position in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where

    conc : ⟦ Box ghost τ ⟧v adv (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- goal : ghost ≤ adv
    -- eq   : 1 ≤ adv
    ... | boxInterpBiobs   eq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiobs eq a1 a2 inner

    ... | boxInterpBiunobs eq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiunobs eq a1 a2 inner

-- var generalisation here
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost {sz} {Γ} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

-------------------------------
-- Unary fundamental theorem
{-
-- Terminating pragma needed because in the (App t1 t2) case we need to recursve with (Promote t2) which doesn't look
-- smaller to Agda
{-# TERMINATING #-}
utheoremg : {{R : Semiring}} {s : ℕ} {γ : List Term}
        -> {Γ : ContextG s} {e : Term} {τ : Type}
        -> Γ ⊢ e ∶ τ
        -> [ Γ ]Γg γ
        -> [ τ ]e (multisubst γ e)
utheoremg {s} {γ} {Γ} {.(Var (Γlength Γ1))} {τ} (var {s1} {s2} {.τ} {.Γ} {Γ1} {Γ2} pos) context v substi
 rewrite pos with Γ1 | γ | context
... | Empty | [] | ()
... | Empty | x ∷ g | (argInterp , restInterp) , infoContext = conc
  where
    conc : [ τ ]v v
    conc with argInterp (Promote x) refl
    ... | boxInterpV t inner = inner v (isSimultaneous' {v} {t} {g} substi)
    
... | Ext k x | [] | ()
-- same as above just moves down the context (bit of fiddly non key stuff)
... | Ext k x | x₁ ∷ g | argInterp , sndrestInterp = {!!}

utheoremg {sz} {γ} {Γ} {App t1 t2} {τ} (app {s} {Γ} {Γ1} {Γ2} {r} {A} {B} typ1 typ2 {pos}) context v1 v1redux
  rewrite pos =
    let
      ((var1 , bod1) , (fun1redux , bodTy1)) = reduxTheoremAppTy {multisubst' 0 γ t1} {multisubst' 0 γ t2} {v1} {0} {Empty} {A} {B} (subst (\r -> multiRedux r ≡ v1) (substPresApp {0} {γ} {t1} {t2}) v1redux) (multiSubstTy {sz} {Γ1} {t1} {FunTy A r B} {γ} typ1)
      fun1 = Abs var1 bod1

      ih1 = utheoremg {sz} {γ} {Γ1} {t1} {FunTy A r B} typ1 (convert context)
      ih1applied = ih1 fun1 fun1redux

      -- Join up the reductions
      -- multiRedux (App (multisubst' 0 γ t1) (multisubst' 0 γ t2)) ≡ v1
      aeq1 = trans (cong multiRedux (sym (substPresApp {0} {γ} {t1} {t2}))) v1redux
      -- multiRedux (App (Abs var1 bod1) (multisubst' 0 γ t2)) ≡ v1
      aeq2 = trans (sym (multReduxCongruence {multisubst' zero γ t1} {Abs var1 bod1} {\t1' -> App t1' (multisubst' 0 γ t2)} fun1redux)) aeq1
      --
      v1reduxerFull = trans (sym (betaVariant1 {bod1} {multisubst' 0 γ t2} {var1})) aeq2

    in extract ih1applied (multisubst' zero γ t2) argument v1 v1reduxerFull
  where
    extract : {x : ℕ} {e : Term} -> [ FunTy A r B ]v (Abs x e)
           -> (forall (v : Term)
                 -> [ Box r A ]e (Promote v)
                 -> [ B ]e (syntacticSubst v x e))
    extract {x} {e} pre with pre
    ... | funInterpV .e  inner = inner


    convertInterp : {A : Type} {r1 r2 : grade} {x : Term} -> [ Box (r1 +R (r *R r2)) A ]e (Promote x) -> [ Box r1 A ]e (Promote x)
    convertInterp {A} {r1} {r2} {x} arg v0 v0redux with arg v0 v0redux
    ... | boxInterpV e inner = boxInterpV e inner

    convert : {sz : ℕ} {γ : List Term} {Γ1 Γ2 : Context sz} -> [ Γ1 ++ (r · Γ2) ]Γ γ -> [ Γ1 ]Γ γ
    convert {.0} {γ} {Empty} {Empty} tt = tt
    convert {suc s} {x ∷ γ} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} (head , tail) =
      convertInterp {A} {r1} {r2} {x} head , convert {s} {γ} {Γ1} {Γ2} tail

    convertInterp2 : {A : Type} {r1 r2 : grade} {x : Term} -> [ Box (r1 +R (r *R r2)) A ]e (Promote x) -> [ Box (r *R r2) A ]e (Promote x)
    convertInterp2 {A} {r1} {r2} {x} arg v0 v0redux with arg v0 v0redux
    ... | boxInterpV e inner = boxInterpV e inner

    convert2 : {sz : ℕ} {γ : List Term} {Γ1 Γ2 : Context sz} -> [ Γ1 ++ (r · Γ2) ]Γ γ -> [ r · Γ2 ]Γ γ
    convert2 {.0} {γ} {Empty} {Empty} tt = tt
    convert2 {suc s} {x ∷ γ} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} (head , tail)
      rewrite sym (sameTypes {s} {Γ1} {Γ2} {Ext (Γ1 ++ Γ2) (Grad A (r1 +R r2))} {A} {A'} {r1} {r2} refl) =
        convertInterp2 {A} {r1} {r2} {x} head , convert2 {s} {γ} {Γ1} {Γ2} tail

    argument : [ Box r A ]e (Promote (multisubst' zero γ t2))
    argument =
      let
        ih2 = utheoremg {sz} {γ} {r ·g Γ2} {Promote t2} {Box r A} (pr {Γ' = r ·g Γ2} {r} typ2 {refl}) (convert2 context)
      in
        subst (\h -> [ Box r A ]e h) (substPresProm {0} {γ} {t2}) ih2

-- # ABS
utheoremg {s} {γ} {Γ'} {Abs .(Γlength Γ1 + 1) t} {FunTy A r B} (abs {s1} {s2} {Γ} {Γ1} {Γ2} {Γ'} pos typing {rel}) context v substi rewrite pos | rel =
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
   body v' arg v1 v1redux rewrite substitutionResult {s1} {v'} {γ} {t} {Γ1} =
     let
      ih = utheoremg {suc (s1 + s2)} {v' ∷ γ}  {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} typing ( arg  , context)
     in ih v1 v1redux

-- # PROMOTION
utheoremg {s} {γ} {Γ'} {Promote t} {Box r A} (pr {_} {Γ} {Γ'} typing {prf}) context v substi rewrite prf =
   let
     ih = utheoremg {s} {γ} {Γ} {t} {A} typing (underBox context)
   in
     subst (\h -> [ Box r A ]v h) thm (boxInterpV (multisubst γ t) ih)
  where
    convert : {s : grade} {v : Term} {A : Type} -> [ Box (r *R s) A ]e (Promote v) -> [ Box s A ]e (Promote v)
    convert {s} {v} {A} pre v0 v0redux with pre v0 v0redux
    ... | boxInterpV e inner = boxInterpV e inner

    underBox : {sz : ℕ} {γ : List Term} {Γ : Context sz} -> [ r · Γ ]Γ γ -> [ Γ ]Γ γ
    underBox {0} {_} {Empty} g = tt
    underBox {suc sz} {v ∷ γ} {Ext Γ (Grad A s)} (ass , g) = convert ass , underBox {sz} {γ} {Γ} g

    thm : Promote (multisubst γ t) ≡ v
    thm =
       let qr = cong multiRedux (substPresProm {0} {γ} {t})
           qr' = trans qr (valuesDontReduce {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym substi) qr')

-- # Unit
utheoremg {_} {γ} {_} {.unit} {.Unit} unitConstr context v substi =
  subst (\h -> [ Unit ]v h) thm unitInterpV
  where
    thm : unit ≡ v
    thm = trans (sym (cong multiRedux (substPresUnit {γ} {0}))) substi

-- # BoolTy
utheoremg {_} {γ} {_} {.vtrue} {.BoolTy} trueConstr context v substi =
 subst (\h -> [ BoolTy ]v h) thm boolInterpTrue
  where
    thm : vtrue ≡ v
    thm = trans (sym (cong multiRedux (substPresTrue {γ} {0}))) substi

utheoremg {_} {γ} {_} {.vfalse} {.BoolTy} falseConstr context v substi =
 subst (\h -> [ BoolTy ]v h) thm boolInterpFalse
  where
    thm : vfalse ≡ v
    thm = trans (sym (cong multiRedux (substPresFalse {γ} {0}))) substi

-- # If
utheoremg {sz} {γ} {Γ} {If tg t1 t2} {B} (if {.sz} {Γ} {Γ1} {Γ2} {.B} {tg} {t1} {t2} {r} {used} typG typ1 typ2 {res}) context v1 v1redux rewrite sym res =
    let
     -- doesn't seem to be used actually here- but more important in the binary case I think
     ih = utheoremg {sz} {γ} {Γ1} {tg} {BoolTy} typG (convert context)
    in caseBody
  where
    v1redux' : multiRedux (If (multisubst γ tg) (multisubst γ t1) (multisubst γ t2))  ≡ v1
    v1redux' = (trans (cong multiRedux (sym (substPresIf {0} {γ} {tg} {t1} {t2}))) v1redux)

    convertHyp : {x : Term} {r1 r2 : grade} {A : Type} -> [ Box ((r *R r1) +R r2) A ]e (Promote x) -> [ Box r1 A ]e (Promote x)
    convertHyp {x} {r1} {r2} pre v0 v0redux with pre v0 v0redux
    ... | boxInterpV e inner = boxInterpV e inner

    convertHyp2 : {x : Term} {r1 r2 : grade} {A : Type} -> [ Box ((r *R r1) +R r2) A ]e (Promote x) -> [ Box r2 A ]e (Promote x)
    convertHyp2 {x} {r1} {r2} pre v0 v0redux with pre v0 v0redux
    ... | boxInterpV e inner = boxInterpV e inner

    convert : {sz : ℕ} {Γ1 Γ2 : Context sz} {γ : List Term} -> [ (r · Γ1) ++ Γ2 ]Γ γ -> [ Γ1 ]Γ γ
    convert {.0} {Empty} {Empty} {γ} g = tt
    convert {.(suc _)} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {[]} ()
    convert {suc sz} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {x ∷ γ} (hd , tl) =
      convertHyp hd , convert {sz} {Γ1} {Γ2} {γ} tl

    convert2 : {sz : ℕ} {Γ1 Γ2 : Context sz} {γ : List Term} -> [ (r · Γ1) ++ Γ2 ]Γ γ -> [ Γ2 ]Γ γ
    convert2 {.0} {Empty} {Empty} {γ} g = tt
    convert2 {.(suc _)} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {[]} ()
    convert2 {suc sz} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {x ∷ γ} (hd , tl)
     rewrite sameTypes {sz} {Γ1} {Γ2} {Ext (Γ1 ++ Γ2) (Grad A (r1 +R r2))} {A} {A'} {r1} {r2} refl =
      convertHyp2 hd , convert2 {sz} {Γ1} {Γ2} {γ} tl

    caseBody : [ B ]v v1
    caseBody with reduxTheoremBool {multisubst γ tg} {multisubst γ t1} {multisubst γ t2} {v1} v1redux'
    ... | inj₁ trueEv  =
      utheoremg {sz} {γ} {Γ2} {t1} {B} typ1 (convert2 context) v1
         (sym (reduxTheoremBool1 {multisubst γ tg} {multisubst γ t1} {multisubst γ t2} {v1} v1redux' trueEv))
    ... | inj₂ falseEv =
      utheoremg {sz} {γ} {Γ2} {t2} {B} typ2 (convert2 context) v1
         (sym (reduxTheoremBool2 {multisubst γ tg} {multisubst γ t1} {multisubst γ t2} {v1} v1redux' falseEv))

-}
--------------------------------------

{-
binaryImpliesUnaryG : {{R : Semiring}} {sz : ℕ} { Γ : Context sz } {adv : grade} {γ1 γ2 : List Term}
                    -> ⟦ Γ ⟧Γ adv γ1 γ2 -> ([ Γ ]Γ γ1) × ([ Γ ]Γ γ2)
binaryImpliesUnaryG {.0} {Empty} {adv} {_} {_} pre = tt , tt
binaryImpliesUnaryG {suc sz} {Ext Γ (Grad A r)} {adv} {v1 ∷ γ1} {v2 ∷ γ2} (arg , rest)
  with binaryImpliesUnary {Box r A} {Promote v1} {Promote v2} {adv} arg | binaryImpliesUnaryG {sz} {Γ} {adv} {γ1} {γ2} rest
  ... | ( arg1 , arg2 ) | ( rest1 , rest2 ) = ( (arg1 , rest1) , (arg2 , rest2) )

{-# TERMINATING #-}
biFundamentalTheoremGhost : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {sz : ℕ}
          {Γ : Context sz} {e : Term} {τ : Type}

        -> Γ ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ ⟧Γ adv γ1 γ2
        -> ⟦ τ ⟧e adv (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost {_} {Γ} {.(Var (Γlength _))} {τ} (var pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}


biFundamentalTheoremGhost {sz} {Γ} {App t1 t2} {.B} (app {s} {Γ} {Γ1} {Γ2} {r} {A} {B} typ1 typ2 {pos}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos =
   let
    -- Reducability of `App t1 t2` implies that there exists a value `Abs var1 bod1` which can be obtained by
    -- reducing `t1` underneath context `γ1` and `Abs var2 bod2` underneath context `γ2`
    ((var1 , bod1) , (fun1redux , bodTy1)) = reduxTheoremAppTy {multisubst' 0 γ1 t1} {multisubst' 0 γ1 t2} {v1} {0} {Empty} {A} {B} (subst (\r -> multiRedux r ≡ v1) (substPresApp {0} {γ1} {t1} {t2}) v1redux) (multiSubstTy {sz} {Γ1} {t1} {FunTy A r B} {γ1} typ1)
    ((var2 , bod2) , (fun2redux , bodTy2)) = reduxTheoremAppTy {multisubst' 0 γ2 t1} {multisubst' 0 γ2 t2} {v2} {0} {Empty} {A} {B} (subst (\r -> multiRedux r ≡ v2) (substPresApp {0} {γ2} {t1} {t2}) v2redux) (multiSubstTy {sz} {Γ1} {t1} {FunTy A r B} {γ2} typ1)
    fun1 = Abs var1 bod1
    fun2 = Abs var2 bod2

   -- Apply binary fundmanetal lemma inductively on left-hand side (t1)
    ih1 = biFundamentalTheoremGhost {sz} {Γ1} {t1} {FunTy A r B} typ1 adv (splitContext1 contextInterp)
    -- This provides the values obtained by the first premise
    ih1applied = ih1  fun1 fun2 fun1redux fun2redux

    -- Join up the reductions
    -- multiRedux (App (multisubst' 0 γ1 t1) (multisubst' 0 γ1 t2)) ≡ v1
    aeq1 = trans (cong multiRedux (sym (substPresApp {0} {γ1} {t1} {t2}))) v1redux
    -- multiRedux (App (Abs var1 bod1) (multisubst' 0 γ1 t2)) ≡ v1
    aeq2 = trans (sym (multReduxCongruence {multisubst' zero γ1 t1} {Abs var1 bod1} {\t1' -> App t1' (multisubst' 0 γ1 t2)} fun1redux)) aeq1
    --
    v1reduxerFull = trans (sym (betaVariant1 {bod1} {multisubst' 0 γ1 t2} {var1})) aeq2

    -- multiRedux (App (multisubst' 0 γ2 t1) (multisubst' 0 γ2 t2)) ≡ v2
    beq1 = trans (cong multiRedux (sym (substPresApp {0} {γ2} {t1} {t2}))) v2redux
    -- multiRedux (App (Abs var1 bod2) (multisubst' 0 γ2 t2)) ≡ v2
    beq2 = trans (sym (multReduxCongruence {multisubst' zero γ2 t1} {Abs var2 bod2} {\t1' -> App t1' (multisubst' 0 γ2 t2)} fun2redux)) beq1
    --
    v2reduxerFull = trans (sym (betaVariant1 {bod2} {multisubst' 0 γ2 t2} {var2})) beq2

   in
     extract ih1applied (multisubst' zero γ1 t2) (multisubst' zero γ2 t2) argument v1 v2 v1reduxerFull v2reduxerFull
  where
    extract : {x y : ℕ} {e1 e2 : Term} -> ⟦ FunTy A r B ⟧v adv (Abs x e1) (Abs y e2)
           -> (forall (v1 : Term) (v2 : Term)
                 -> ⟦ Box r A ⟧e adv (Promote v1) (Promote v2)
                 -> ⟦ B ⟧e adv (syntacticSubst v1 x e1) (syntacticSubst v2 y e2))
    extract {x} {y} {e1} {e2} pre with pre
    ... | funInterpBi .e1 .e2 inner _ _ = inner

    convertVal2 : {r1 r2 : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R (r *R r2)) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box (r *R r2) A ⟧v adv (Promote v1) (Promote v2)
    convertVal2 {r1} {r2} {v1} {v2} {A} (boxInterpBiobs eq .v1 .v2 arg) with (r1 +R (r *R r2)) ≤d adv | (r *R r2) ≤d adv
    ... | no eqo  | yes eq' = ⊥-elim (eqo eq)
    ... | no eqo  | no eq'  = boxInterpBiunobs  eq' v1 v2 (binaryImpliesUnary {A} {v1} {v2} {adv} arg)    
    ... | yes eqo | yes eq' = boxInterpBiobs   eq' v1 v2 arg
    ... | yes eqo | no eq'  = boxInterpBiunobs  eq' v1 v2 (binaryImpliesUnary {A} {v1} {v2} {adv} arg)
    convertVal2 {r1} {r2} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 argInterp) = boxInterpBiunobs (propInvPlusMono2 eq) v1 v2 argInterp

    convertVal : {r1 r2 : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R (r *R r2)) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r1 A ⟧v adv (Promote v1) (Promote v2)
    convertVal {r1} {r2} {v1} {v2} {A} (boxInterpBiobs eq .v1 .v2 arg) with r1 ≤d adv
    ... | no  eqo = boxInterpBiunobs eqo v1 v2 ((binaryImpliesUnary {A} {v1} {v2} {adv} arg))
    ... | yes eqo = boxInterpBiobs eqo v1 v2 arg
    convertVal {r1} {r2} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 argInterp) = boxInterpBiunobs (propInvPlusMono1 eq) v1 v2 argInterp

    convert : {r1 r2 : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R (r *R r2)) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box r1 A ⟧e adv (Promote v1) (Promote v2)
    convert {r1} {r2} {v1} {v2} {A} arg v1' v2' v1redux' v2redux'
      rewrite trans (sym v1redux') (reduxProm {v1})
            | trans (sym v2redux') (reduxProm {v2}) = convertVal {r1} {r2} {v1} {v2} {A} (arg (Promote v1) ((Promote v2)) refl refl)

    splitContext1 : {sz : ℕ} {γ1 γ2 : List Term} {Γ1 Γ2 : Context sz} -> ⟦ Γ1 ++ (r · Γ2) ⟧Γ adv γ1 γ2 -> ⟦ Γ1 ⟧Γ adv γ1 γ2
    splitContext1 {0} {γ1} {γ2} {Empty} {Empty} _ = tt
    splitContext1 {.(suc _)} {[]} {[]} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} ()
    splitContext1 {.(suc _)} {[]} {x ∷ γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} ()
    splitContext1 {.(suc _)} {x ∷ γ1} {[]} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} ()
    splitContext1 {(suc s)} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} (arg , rest) =
      convert {r1} {r2} {v1} {v2} {A} arg , splitContext1 {s} {γ1} {γ2} {Γ1} {Γ2} rest

    convert2 : {r1 r2 : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R (r *R r2)) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box (r *R r2) A ⟧e adv (Promote v1) (Promote v2)
    convert2 {r1} {r2} {v1} {v2} {A} arg v1' v2' v1redux' v2redux'
      rewrite trans (sym v1redux') (reduxProm {v1})
            | trans (sym v2redux') (reduxProm {v2}) = convertVal2 {r1} {r2} {v1} {v2} {A} (arg (Promote v1) ((Promote v2)) refl refl)

    splitContext2 : {sz : ℕ} {γ1 γ2 : List Term} {Γ1 Γ2 : Context sz} -> ⟦ Γ1 ++ (r · Γ2) ⟧Γ adv γ1 γ2 -> ⟦ r · Γ2 ⟧Γ adv γ1 γ2
    splitContext2 {0} {γ1} {γ2} {Empty} {Empty} _ = tt
    splitContext2 {.(suc _)} {[]} {[]} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} ()
    splitContext2 {.(suc _)} {[]} {x ∷ γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} ()
    splitContext2 {.(suc _)} {x ∷ γ1} {[]} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} ()
    splitContext2 {(suc s)} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} (arg , rest)
      rewrite sym (sameTypes {s} {Γ1} {Γ2} {Ext (Γ1 ++ Γ2) (Grad A (r1 +R r2))} {A} {A'} {r1} {r2} refl) =
        convert2 {r1} {r2} {v1} {v2} {A} arg , splitContext2 {s} {γ1} {γ2} {Γ1} {Γ2} rest

    argument : ⟦ Box r A ⟧e adv (Promote (multisubst γ1 t2)) (Promote (multisubst γ2 t2))
    argument =
      let ih2 = biFundamentalTheoremGhost {sz} {r · Γ2} {Promote t2} {Box r A} (pr {Γ' = r · Γ2} {r} typ2 {refl}) {γ1} {γ2} adv (splitContext2 contextInterp)
      in subst₂ (\h1 h2 -> ⟦ Box r A ⟧e adv h1 h2) (substPresProm {0} {γ1} {t2}) (substPresProm {0} {γ2} {t2}) ih2

-- # ABS
biFundamentalTheoremGhost {sz} {Γ'} {Abs .(Γlength Γ1 + 1) t} {FunTy A r B} (abs {s1} {s2} {Γ} {Γ1} {Γ2} {Γ'} pos typ {rel}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ FunTy A r B ⟧v adv h1 h2) (thm γ1 v1 v1redux) (thm γ2 v2 v2redux) (funInterpBi {adv} {A} {B} {r} {Γlength Γ1 + 1} {Γlength Γ1 + 1} (multisubst γ1 t) ((multisubst γ2 t)) body ubody1 ubody2)
  where
    body : (forall (v1' : Term) (v2' : Term)
         -> ⟦ Box r A ⟧e adv (Promote v1') (Promote v2')
         -> ⟦ B ⟧e adv (syntacticSubst v1' (Γlength Γ1 + 1) (multisubst γ1 t)) (syntacticSubst v2' (Γlength Γ1 + 1) (multisubst γ2 t)))
    body v1' v2' arg rewrite pos | rel | (substitutionResult {s1} {v1'} {γ1} {t} {Γ1}) | (substitutionResult {s1} {v2'} {γ2} {t} {Γ1}) =
      biFundamentalTheoremGhost {suc (s1 + s2)} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} typ {v1' ∷ γ1} {v2' ∷ γ2} adv (arg , contextInterp)

    ubody1 : (v : Term) →
      [ Box r A ]e (Promote v) →
      [ B ]e (syntacticSubst v (Γlength Γ1 + 1) (multisubst γ1 t))
    ubody1 v arg rewrite pos | rel | substitutionResult {s1} {v} {γ1} {t} {Γ1} = utheoremg {suc (s1 + s2)} {v ∷ γ1} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} typ (arg , proj₁ (binaryImpliesUnaryG contextInterp))

    ubody2 : (v : Term) →
      [ Box r A ]e (Promote v) →
      [ B ]e (syntacticSubst v (Γlength Γ1 + 1) (multisubst γ2 t))
    ubody2 v arg rewrite pos | rel | substitutionResult {s1} {v} {γ2} {t} {Γ1} = utheoremg {suc (s1 + s2)} {v ∷ γ2} {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} typ (arg , proj₂ (binaryImpliesUnaryG contextInterp))

    thm : (γ : List Term) -> (v : Term)
        -> multiRedux (multisubst γ (Abs (Γlength Γ1 + 1) t)) ≡ v -> Abs (Γlength Γ1 + 1) (multisubst γ t) ≡ v
    thm γ v redux =
     let
       qr = cong multiRedux (substPresAbs {0} {γ} {Γlength Γ1 + 1} {t})
       qr' = trans qr (valuesDontReduce {Abs (Γlength Γ1 + 1) (multisubst γ t)} (absValue {Γlength Γ1 + 1} (multisubst γ t)))
     in sym (trans (sym redux) qr')

-- # PROMOTION
biFundamentalTheoremGhost {sz} {Γ'} {Promote t} {Box r A} (pr {s} {Γ} {Γ'} typ {prf}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux with r ≤d adv
... | no eq rewrite prf =
  let
    (uinterp1 , uinterp2) = underBox {sz} {γ1} {γ2} {Γ} contextInterp
    ih1 = utheoremg {s} {γ1} {Γ} {t} {A} typ uinterp1
    ih2 = utheoremg {s} {γ2} {Γ} {t} {A} typ uinterp2
  in
   subst₂ (\h1 h2 -> ⟦ Box r A ⟧v adv h1 h2) (thm {v1} {γ1} v1redux) (thm {v2} {γ2} v2redux)
             (boxInterpBiunobs eq (multisubst γ1 t) (multisubst γ2 t) (ih1 , ih2))
  where
    thm : {v : Term} {γ : List Term} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
    thm {v} {γ} redux =
       let qr = cong multiRedux (substPresProm {0} {γ} {t})
           qr' = trans qr (valuesDontReduce {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')

    binaryToUnaryVal : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ([ Box s A ]v (Promote v1)) × ([ Box s A ]v (Promote v2))
    binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpBiobs eq' .v1 .v2 ainterp) =
      let (a , b) = binaryImpliesUnary {A} {v1} {v2} {adv} ainterp in (boxInterpV v1 a , boxInterpV v2 b)

    binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 (left , right)) = (boxInterpV v1 left) , (boxInterpV v2 right)

    binaryToUnaryExp : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ([ Box s A ]e (Promote v1)) × ([ Box s A ]e (Promote v2))
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
    underBox {suc sz} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A r')} (arg , g) =
     let
      (left , right) = underBox {sz} {γ1} {γ2} {Γ} g
      (l , r) = binaryToUnaryExp arg
     in
       (l , left) , (r , right)

--------------------------------------------------------
... | yes eq rewrite prf =
  let
    ih = biFundamentalTheoremGhost {sz} {Γ} {t} {A} typ {γ1} {γ2} adv (underBox {sz} {γ1} {γ2} contextInterp)
  in
    subst₂ (\h1 h2 -> ⟦ Box r A ⟧v adv h1 h2) (thm {v1} {γ1} v1redux) (thm {v2} {γ2} v2redux) (boxInterpBiobs eq (multisubst γ1 t) (multisubst γ2 t) ih)

  where

    convertVal : {s : grade} {v1 : Term} {v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧v adv (Promote v1) (Promote v2)
    convertVal {s} {v1} {v2} {A} (boxInterpBiobs prop .v1 .v2 interp) with s ≤d adv
    ... | yes eq = boxInterpBiobs eq v1 v2 interp
    ... | no eq  = boxInterpBiunobs eq v1 v2 (binaryImpliesUnary {A} {v1} {v2} interp)

    convertVal {s} {v1} {v2} {A} (boxInterpBiunobs x .v1 .v2 interp) = boxInterpBiunobs (propInvTimesMonoAsym x eq) v1 v2 interp

    convertExp : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧e adv (Promote v1) (Promote v2)
    convertExp {s} {v1} {v2} {A} arg1 v1' v2' v1redux' v2redux' rewrite trans (sym v1redux') (reduxProm {v1}) | trans (sym v2redux') (reduxProm {v2}) =
       convertVal  {s} {v1} {v2} {A} (arg1 (Promote v1) (Promote v2) refl refl)

    underBox : {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> ⟦ Γ ⟧Γ adv γ1 γ2
    underBox {_} {_} {_} {Empty}   g = tt
    underBox {suc n} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A s)} (ass , g) = convertExp {s} {v1} {v2} {A} ass , underBox {n} {γ1} {γ2} {Γ} g
    underBox {_} {[]} {[]} {Ext Γ (Grad A r₁)} ()
    underBox {_} {[]} {x ∷ γ5} {Ext Γ (Grad A r₁)} ()
    underBox {_} {x ∷ γ4} {[]} {Ext Γ (Grad A r₁)} ()

    thm : {v : Term} {γ : List Term} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
    thm {v} {γ} redux =
       let qr = cong multiRedux (substPresProm {0} {γ} {t})
           qr' = trans qr (valuesDontReduce {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')

biFundamentalTheoremGhost {_} {_} {.unit} {.Unit} unitConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ Unit ⟧v adv h1 h2) thm1 thm2 (unitInterpBi {adv})
    where
      thm1 : unit ≡ v1
      thm1 = trans (sym (cong multiRedux (substPresUnit {γ1} {0}))) v1redux

      thm2 : unit ≡ v2
      thm2 = trans (sym (cong multiRedux (substPresUnit {γ2} {0}))) v2redux


biFundamentalTheoremGhost {_} {_} {.vtrue} {.BoolTy} trueConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ BoolTy ⟧v adv h1 h2) thm1 thm2 boolInterpTrueBi
   where
    thm1 : vtrue ≡ v1
    thm1 = trans (sym (cong multiRedux (substPresTrue {γ1} {0}))) v1redux

    thm2 : vtrue ≡ v2
    thm2 = trans (sym (cong multiRedux (substPresTrue {γ2} {0}))) v2redux

biFundamentalTheoremGhost {_} {_} {.vfalse} {.BoolTy} falseConstr {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
  subst₂ (\h1 h2 -> ⟦ BoolTy ⟧v adv h1 h2) thm1 thm2 boolInterpFalseBi
   where
    thm1 : vfalse ≡ v1
    thm1 = trans (sym (cong multiRedux (substPresFalse {γ1} {0}))) v1redux

    thm2 : vfalse ≡ v2
    thm2 = trans (sym (cong multiRedux (substPresFalse {γ2} {0}))) v2redux

biFundamentalTheoremGhost {sz} {Γ} {If tg t1 t2} {B} (if {s} {Γ} {Γ1} {Γ2} {.B} {.tg} {.t1} {.t2} {r} {used} typG typ1 typ2 {res})
  {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite sym res =
     caseBody
  where

       v1redux' : multiRedux (If (multisubst γ1 tg) (multisubst γ1 t1) (multisubst γ1 t2))  ≡ v1
       v1redux' = (trans (cong multiRedux (sym (substPresIf {0} {γ1} {tg} {t1} {t2}))) v1redux)

       v2redux' : multiRedux (If (multisubst γ2 tg) (multisubst γ2 t1) (multisubst γ2 t2))  ≡ v2
       v2redux' = (trans (cong multiRedux (sym (substPresIf {0} {γ2} {tg} {t1} {t2}))) v2redux)

       boolDisc : true ≡ false -> ⊥
       boolDisc ()

       convertHyp : {x y : Term} {r1 r2 : grade} {A : Type}
                  -> ⟦ Box ((r *R r1) +R r2) A ⟧e adv (Promote x) (Promote y) -> ⟦ Box r1 A ⟧e adv (Promote x) (Promote y)
       convertHyp {x} {y} {r1} {r2} {A} pre v0 v1 v0redux v1redux with pre v0 v1 v0redux v1redux | r1 ≤d adv
       ... | boxInterpBiobs   eq' t1 t2 inner | yes eq  = boxInterpBiobs eq t1 t2 inner
       ... | boxInterpBiobs   eq' t1 t2 inner | no eq   = boxInterpBiunobs eq t1 t2 (binaryImpliesUnary {A} {t1} {t2} {adv} inner)
       ... | boxInterpBiunobs eq' t1 t2 inner | yes eq  = ⊥-elim ((propertyConditionalNI eq' used) eq)
       ... | boxInterpBiunobs eq' t1 t2 inner | no eq   = boxInterpBiunobs eq t1 t2 inner

       convertHyp2 : {x y : Term} {r1 r2 : grade} {A : Type}
                   -> ⟦ Box ((r *R r1) +R r2) A ⟧e adv (Promote x) (Promote y) -> ⟦ Box r2 A ⟧e adv (Promote x) (Promote y)
       convertHyp2 {x} {y} {r1} {r2} {A} pre v0 v1 v0redux v1redux with pre v0 v1 v0redux v1redux | r2 ≤d adv
       ... | boxInterpBiobs    eq' t1 t2 inner  | yes eq  = boxInterpBiobs eq t1 t2 inner
       ... | boxInterpBiobs    eq' t1 t2 inner  | no eq   = boxInterpBiunobs eq t1 t2 (binaryImpliesUnary {A} {t1} {t2} {adv} inner)
       ... | boxInterpBiunobs  eq' t1 t2 inner  | yes eq  = ⊥-elim ((propertyConditionalNI2 eq' used) eq)
       ... | boxInterpBiunobs  eq' t1 t2 inner  | no eq   = boxInterpBiunobs eq t1 t2 inner

       convert : {sz : ℕ} {Γ1 Γ2 : Context sz} {γ1 γ2 : List Term} -> ⟦ (r · Γ1) ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ1 ⟧Γ adv γ1 γ2
       convert {.0} {Empty} {Empty} {γ1} {γ2} g = tt
       convert {suc sz} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {x1 ∷ γ1} {x2 ∷ γ2} (hd , tl) =
          convertHyp hd , convert {sz} {Γ1} {Γ2} {γ1} {γ2} tl

       convert2 : {sz : ℕ} {Γ1 Γ2 : Context sz} {γ1 γ2 : List Term} -> ⟦ (r · Γ1) ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ2 ⟧Γ adv γ1 γ2
       convert2 {.0} {Empty} {Empty} {γ1} {γ2} _ = tt
       convert2 {.(suc _)} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {[]} {[]} ()
       convert2 {suc sz} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {x1 ∷ γ1} {x2 ∷ γ2} (hd , tl)
         rewrite sameTypes {sz} {Γ1} {Γ2} {Ext (Γ1 ++ Γ2) (Grad A (r1 +R r2))} {A} {A'} {r1} {r2} refl =
           convertHyp2 hd , convert2 {sz} {Γ1} {Γ2} {γ1} {γ2} tl

       -- induct on boolean to determine which (pairs of) values are valid
       ih : ⟦ BoolTy ⟧e adv (multisubst γ1 tg) (multisubst γ2 tg)
       ih = biFundamentalTheoremGhost {sz} {Γ1} {tg} {BoolTy} typG {γ1} {γ2} adv (convert contextInterp)

      -- induct on the case bodies depending on what values appear
       caseBody : ⟦ B ⟧v adv v1 v2
       caseBody with reduxTheoremBool {multisubst γ1 tg} {multisubst γ1 t1} {multisubst γ1 t2} {v1} v1redux'
                    | reduxTheoremBool {multisubst γ2 tg} {multisubst γ2 t1} {multisubst γ2 t2} {v2} v2redux'
       caseBody | inj₁ trueEv1 | inj₁ trueEv2 =
         biFundamentalTheoremGhost {sz} {Γ2} {t1} {B} typ1 {γ1} {γ2} adv (convert2 contextInterp) v1 v2
           (sym (reduxTheoremBool1 {multisubst γ1 tg} {multisubst γ1 t1} {multisubst γ1 t2} {v1} v1redux' trueEv1))
             (sym (reduxTheoremBool1 {multisubst γ2 tg} {multisubst γ2 t1} {multisubst γ2 t2} {v2} v2redux' trueEv2))
       caseBody | inj₁ trueEv1  | inj₂ falseEv2 with ih vtrue vfalse trueEv1 falseEv2
       ... | ()
       caseBody | inj₂ falseEv1 | inj₁ trueEv2  with ih vfalse vtrue falseEv1 trueEv2
       ... | ()
       caseBody | inj₂ falseEv1 | inj₂ falseEv2 =
         biFundamentalTheoremGhost {sz} {Γ2} {t2} {B} typ2 {γ1} {γ2} adv (convert2 contextInterp) v1 v2
           (sym (reduxTheoremBool2 {multisubst γ1 tg} {multisubst γ1 t1} {multisubst γ1 t2} {v1} v1redux' falseEv1))
             (sym (reduxTheoremBool2 {multisubst γ2 tg} {multisubst γ2 t1} {multisubst γ2 t2} {v2} v2redux' falseEv2))

lem : {{R : Semiring}} {adv : grade}
      {A : Type} {v1 v2 : Term}
   -> Value v1
   -> Value v2
   -> ⟦ A ⟧e adv v1 v2
   -> ⟦ A ⟧v adv v1 v2

lem {adv} {A} {v1} {v2} isvalv1 isvalv2 mem =
  mem v1 v2 (valuesDontReduce {v1} isvalv1) (valuesDontReduce {v2} isvalv2)

boolBinaryValueInterpEquality : {{R : Semiring}} {r : grade} (v1 v2 : Term) -> ⟦ BoolTy ⟧v r v1 v2 -> v1 ≡ v2
boolBinaryValueInterpEquality .vtrue .vtrue boolInterpTrueBi = refl
boolBinaryValueInterpEquality .vfalse .vfalse boolInterpFalseBi = refl

boolBinaryExprInterpEquality : {{R : Semiring}} {r : grade} (v1 v2 : Term)
                              -> ⟦ BoolTy ⟧e r v1 v2
                              -> multiRedux v1 ≡ multiRedux v2
boolBinaryExprInterpEquality t1 t2 prf =
  boolBinaryValueInterpEquality (multiRedux t1) (multiRedux t2) ((prf (multiRedux t1) (multiRedux t2) refl refl))

-- Value lemma for promotion
promoteValueLemma : {{R : Semiring}} {v : Term} {r : grade} {A : Type}

  -> Empty ⊢ v ∶ Box r A
  -> Value v
  -> Σ Term (\v' -> v ≡ Promote v')

promoteValueLemma {_} {r} () varValue

promoteValueLemma typing (promoteValue t) = t , refl

-- Non-interference
nonInterfSpecialised :
   {{R : Semiring}} {{R' : NonInterferingSemiring R}}
   {A : Type} {e : Term} {r s : grade} {pre : r ≤ s} {nonEq : r ≢ s}
        -> Ext Empty (Grad A s) ⊢ e ∶ Box r BoolTy

        -> (v1 v2 : Term)
        -> Empty ⊢ v1 ∶ A
        -> Empty ⊢ v2 ∶ A
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) == multiRedux (syntacticSubst v2 0 e)

nonInterfSpecialised {{_}} {{_}} {A} {e} {r} {s} {pre} {nonEq} typing v1 v2 v1typing v2typing isvalv1 isvalv2 with
    -- Apply fundamental binary theorem to v1
    biFundamentalTheoremGhost {zero} {Empty} {Promote v1} {Box s A}
                  (pr v1typing {refl}) {[]} {[]} r tt (Promote v1) (Promote v1)
                  (valuesDontReduce {Promote v1} (promoteValue v1))
                  (valuesDontReduce {Promote v1} (promoteValue v1))
    -- Apply fundamental binary theorem to v2
  | biFundamentalTheoremGhost {zero} {Empty} {Promote v2} {Box s A}
                  (pr v2typing {refl})  {[]} {[]} r tt (Promote v2) (Promote v2)
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  (valuesDontReduce {Promote v2} (promoteValue v2))
... | boxInterpBiobs pre1 .v1 .v1 inner1 | _                                    = ⊥-elim (nonEq (antisymmetry pre pre1))
... | boxInterpBiunobs pre1 .v1 .v1 inner1 | boxInterpBiobs pre2 .v2 .v2 inner2 = ⊥-elim (nonEq (antisymmetry pre pre2))
... | boxInterpBiunobs pre1 .v1 .v1 (valv1 , valv1') | boxInterpBiunobs pre2 .v2 .v2 (valv2 , valv2') =
 let
   -- Show that substituting v1 and evaluating yields a value
   -- and since it is a graded modal type then this value is necessarily
   -- of the form Promote v1''
   substTy1 = substitution {zero} {zero} {Ext Empty (Grad A s)} {Empty} {Empty} {Empty} {s} typing refl v1typing
   (v1'' , prf1) = promoteValueLemma {_} {r} {BoolTy} (preservation {zero} {Empty} {Box r BoolTy} {syntacticSubst v1 0 e} substTy1) (multiReduxProducesValues substTy1)

   -- ... same as above but for v2 ... leading to result of Promote v2''
   substTy2  = substitution {zero} {zero} {Ext Empty (Grad A s)} {Empty} {Empty} {Empty} {s} typing refl v2typing
   (v2'' , prf2) = promoteValueLemma {_} {r} {BoolTy} (preservation {zero} substTy2) (multiReduxProducesValues substTy2)

   -- Apply fundamental binary theorem on the result with the values coming from syntacitcally substituting
   -- then evaluating
   res = biFundamentalTheoremGhost {1} {Ext Empty (Grad A s)} {e} {Box r BoolTy} typing {v1 ∷ []} {v2 ∷ []} r
          (inner valv1' valv2' , tt) (Promote v1'') (Promote v2'') prf1 prf2


   -- Boolean typed (low) values are equal inside the binary interepration
   boolTyEq = boolBinaryExprInterpEquality v1'' v2'' (unpack res)

   -- Plug together the equalities
     -- Promote
   eq = PromoteEq {v1''} {v2''} (embedReduxCong {v1''} {v2''} boolTyEq)
   eq2 = transFullBetaEq (embedEq prf1) eq

 in transFullBetaEq eq2 (embedEq (sym prf2))
   where

     inner : [ A ]e v1 -> [ A ]e v2 -> ⟦ Box s A ⟧e r (Promote v1) (Promote v2)
     inner av1 av2 v3 v4 v3redux v4redux
       rewrite trans (sym v3redux) (valuesDontReduce {Promote v1} (promoteValue v1))
             | trans (sym v4redux) (valuesDontReduce {Promote v2} (promoteValue v2)) =
       boxInterpBiunobs pre1 v1 v2 (av1 , av2)

     -- Helper to unpack interpretation type
     unpack : {v1 v2 : Term} -> ⟦ Box r BoolTy ⟧v r (Promote v1) (Promote v2) -> ⟦ BoolTy ⟧e r v1 v2
     unpack {v1} {v2} (boxInterpBiobs _ .v1 .v2 innerExprInterp) = innerExprInterp
     unpack {v1} {v2} (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = ⊥-elim (eq (reflexive≤ {r}))

-}
