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
open import Data.Maybe.Properties

open import Semiring

-- open Semiring.Semiring {{...}} public
-- open NonInterferingSemiring  {{...}} public
-- open InformationFlowSemiring {{...}} public

open import RelationalModel

data InfoContext {{ R : Semiring }} : (r : grade) (adv : grade) -> Set where
  Visible :   {r adv : grade}  -> r ≤ adv -> InfoContext r adv
  Invisible : {r adv : grade}  -> ¬ (r ≤ adv) -> InfoContext r adv

-- Contexts

-- unary
[_]Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> List Term -> Set
[ (Γ , ghostGrade) ]Γg γ = [ Γ ]Γ γ × ⊤

-- binary
⟦_⟧Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> (adv : grade) -> List Term -> List Term -> Set
⟦ (Γ , ghostGrade)   ⟧Γg adv γ1 γ2 = ⟦ Γ ⟧Γ adv γ1 γ2 × InfoContext ghostGrade adv

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

multiSubstTyG : {{R : Semiring}} {{R' : InformationFlowSemiring R }} -> {n : ℕ} {Γ : ContextG n} {t : Term} {A : Type} {γ : List Term} {ghost : grade} -> Γ ⊢ t ∶ A -> (Empty , ghost) ⊢ multisubst' 0 γ t ∶ A
multiSubstTyG = {!!}

reduxTheoremAppTyG : {{R : Semiring}} {{R' : InformationFlowSemiring R }}
                 -> {t1 t2 v : Term} {s : ℕ} {Γ : Context s} {A B : Type} {r : grade} {ghost : grade}
                 -> multiRedux (App t1 t2) ≡ v
                 -> (Γ , ghost) ⊢ t1 ∶ FunTy A r B
                 -> Σ (ℕ × Term) (\(z , v1') -> multiRedux t1 ≡ Abs z v1' × (((Ext Γ (Grad A r)) , ghost) ⊢ (Abs z v1') ∶  B))
reduxTheoremAppTyG = {!!}


promoteLemma : {t t' t'' : Term} -> Promote t ≡ t' -> Σ Term (\t'' -> Promote t'' ≡ t')
promoteLemma {t} {t'} {t''} pre = t , pre

{-
-- # IDEA 1
{-# TERMINATING #-}
biFundamentalTheoremGhost : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
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
-}

-- Helper to unpack interpretation type
unpackObs : {{R : Semiring}} {A : Type} {v1 v2 : Term} {r adv : grade}
          -> (r ≤ adv)
          -> ⟦ Box r A ⟧v adv (Promote v1) (Promote v2) -> ⟦ A ⟧e adv v1 v2
unpackObs {A} {v1} {v2} {r} {adv} pre (boxInterpBiobs _ .v1 .v2 innerExprInterp) = innerExprInterp
unpackObs {A} {v1} {v2} {r} {adv} pre (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = ⊥-elim (eq pre)

unpackUnobs : {{R : Semiring}} {A : Type} {v1 v2 : Term} {r adv : grade}
          -> ¬ (r ≤ adv)
          -> ⟦ Box r A ⟧v adv (Promote v1) (Promote v2) -> ([ A ]e v1 × [ A ]e v2)
unpackUnobs {A} {v1} {v2} {r} {adv} pre (boxInterpBiobs eq .v1 .v2 innerExprInterp) = ⊥-elim (pre eq)
unpackUnobs {A} {v1} {v2} {r} {adv} pre (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = innerExprInterp

unpackEvidence : {{R : Semiring}}
                 {s : ℕ}
                 { Γ Γ1 Γ2 : ContextG s }
                 {r : grade}
                 (rel : just Γ ≡ (Γ1 ++g (r ·g Γ2)))
               -> Σ grade (\ghost ->
                    Σ (Context s × grade) (\(Γ1' , g1) ->
                      Σ (Context s × grade) (\(Γ2' , g2) ->
                        (Γ ≡ (Γ1' ++ (r · Γ2') , ghost))
                      × (Γ1 ≡ (Γ1' , g1))
                      × (Γ2 ≡ (Γ2' , g2))
                      × (just ghost ≡ partialJoin g1 (r *R g2))
                    )
                   )
                  )
unpackEvidence {s = s} {Γ} {fst , snd} {fst₁ , snd₁} {r} rel = {!!}

justInj : {A : Set} {a1 a2 : A} -> just a1 ≡ just a2 -> a1 ≡ a2
justInj {A} {a1} {.a1} refl = refl

-------------------------------
-- Unary fundamental theorem

-- Terminating pragma needed because in the (App t1 t2) case we need to recursve with (Promote t2) which doesn't look
-- smaller to Agda
{-# TERMINATING #-}
utheoremGhost : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ} {γ : List Term}
        -> {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}
        -> (Γ , ghost) ⊢ e ∶ τ
        -> [ Γ ]Γ γ
        -> [ Box ghost τ ]v (Promote (multisubst γ e))
utheoremGhost {{R}} {sz} {γ} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {s1} {s2} {.τ} {.(Γ , ghost)} {Γ1} {Γ2} pos) context  rewrite injPair1 pos with Γ1 | γ | context
... | Empty | [] | ()
... | Empty | a ∷ γ' | argInterp , restInterp = conc
  where
    conc : [ Box ghost τ ]v (Promote (multisubst (a ∷ γ') (Var 0))) 
    conc = ?

-- same as above just moves down the context (bit of fiddly non key stuff)
... | Ext k x | x₁ ∷ g | argInterp , sndrestInterp = {!!}

utheoremGhost {{R}} {sz} {γ} {Γ} {ghost} {e} {τ} typ context = {!!}

biFundamentalTheoremGhost' : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ ⟧Γ adv γ1 γ2
        -> ⟦ Box ghost τ ⟧v adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))

biFundamentalTheoremGhost' {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp
 rewrite injPair1 pos | sym (injPair2 pos) with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as position in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | (argInterp , restInterp) = conc

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


biFundamentalTheoremGhost' {sz} {Γ} {ghost} {App t1 t2} {.B} (app {.sz} {Γ , ghost} {Γ1 , g1} {Γ2 , g2} {r} {A} {B} typ1 typ2 {pos}) {γ1} {γ2} adv contextInterp with unpackEvidence pos
biFundamentalTheoremGhost' {sz = sz} {Γ} {ghost} {App t1 t2} {.B} (app {.sz} {Γ , ghost} {Γ1 , g1} {Γ2 , g2} {r} {A} {B} typ1 typ2 {pos}) {γ1} {γ2} adv contextInterp | ghosto , ((G1' , g1o) ,  ((G2' , g2o) ,  outer , left , right , gj)) rewrite injPair1 outer | sym (injPair2 outer) | sym (injPair1 left)| sym (injPair2 left) | sym (injPair1 right) | sym (injPair2 right) = main
  where
-- ———————————————————————————————————————————————
    extract : {x y : ℕ} {e1 e2 : Term} -> ⟦ FunTy A r B ⟧v adv (Abs x e1) (Abs y e2)
           -> (forall (v1 : Term) (v2 : Term)
                 -> ⟦ Box r A ⟧e adv (Promote v1) (Promote v2)
                 -> ⟦ B ⟧e adv (syntacticSubst v1 x e1) (syntacticSubst v2 y e2))
    extract {x} {y} {e1} {e2} pre with pre
    ... | funInterpBi .e1 .e2 inner _ _ = inner

    extractUn : {x : ℕ} {e1 : Term} -> [ FunTy A r B ]v (Abs x e1)
           -> (forall (v1 : Term)
                 -> [ Box r A ]e (Promote v1)
                 -> [ B ]e (syntacticSubst v1 x e1))
    extractUn {x} {e1} pre with pre
    ... | funInterpV .e1 inner = inner

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

    main : ⟦ Box ghost B ⟧v adv (Promote (multisubst' 0 γ1 (App t1 t2))) (Promote (multisubst' 0 γ2 (App t1 t2)))
    -- Apply binary fundmanetal lemma inductively on left-hand side (t1)
    main with ghost ≤d adv | biFundamentalTheoremGhost' {sz} {Γ1} {g1} {t1} {FunTy A r B} typ1 {γ1} {γ2} adv (splitContext1 contextInterp)
                           | biFundamentalTheoremGhost' {sz} {r · Γ2} {r *R g2} {Promote t2} {Box r A} (pr {Γ' = (r · Γ2 , r *R g2)} {r} typ2 {refl}) {γ1} {γ2} adv (splitContext2 contextInterp)
    main | yes p | boxInterpBiobs   eq .(multisubst' 0 γ1 t1) .(multisubst' 0 γ2 t1) inner
                | boxInterpBiobs eq' .(multisubst' 0 γ1 (Promote t2)) .(multisubst' 0 γ2 (Promote t2)) argInner
     rewrite (substPresProm {0} {γ1} {t2}) | (substPresProm {0} {γ2} {t2}) = boxInterpBiobs p (multisubst' zero γ1 (App t1 t2)) (multisubst' zero γ2 (App t1 t2)) obsMain
       where
          obsMain : ⟦ B ⟧e adv (multisubst' 0 γ1 (App t1 t2)) (multisubst' 0 γ2 (App t1 t2))
          obsMain v1 v2 v1redux v2redux =
            let
              -- Reducability of `App t1 t2` implies that there exists a value `Abs var1 bod1` which can be obtained by
              -- reducing `t1` underneath context `γ1` and `Abs var2 bod2` underneath context `γ2`
              ((var1 , bod1) , (fun1redux , bodTy1)) = reduxTheoremAppTyG {multisubst' 0 γ1 t1} {multisubst' 0 γ1 t2} {v1} {0} {Empty} {A} {B} {r} {g1} (subst (\r -> multiRedux r ≡ v1) (substPresApp {0} {γ1} {t1} {t2}) v1redux) (multiSubstTyG {sz} {Γ1 , g1} {t1} {FunTy A r B} {γ1} typ1)
              ((var2 , bod2) , (fun2redux , bodTy2)) = reduxTheoremAppTyG {multisubst' 0 γ2 t1} {multisubst' 0 γ2 t2} {v2} {0} {Empty} {A} {B} {r} {g1} (subst (\r -> multiRedux r ≡ v2) (substPresApp {0} {γ2} {t1} {t2}) v2redux) (multiSubstTyG {sz} {Γ1 , g1} {t1} {FunTy A r B} {γ2} typ1)
              fun1 = Abs var1 bod1
              fun2 = Abs var2 bod2

              ih1applied = inner fun1 fun2 fun1redux fun2redux

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

              foo = extract ih1applied (multisubst γ1 t2) (multisubst γ2 t2) argInner v1 v2 v1reduxerFull v2reduxerFull

            in foo

    main | yes p | _ | boxInterpBiunobs eq2 .(multisubst' 0 γ1 (Promote t2)) .(multisubst' 0 γ2 (Promote t2)) argInner =
     ⊥-elim (eq2 (joinMonoInv1 {g1} {r *R g2} {adv} {ghost} gj p))

    main | yes p | boxInterpBiunobs eq .(multisubst' 0 γ1 t1) .(multisubst' 0 γ2 t1) inner  | _ =
     ⊥-elim (eq (joinMonoInv2 {g1} {r *R g2} {adv} {ghost} gj p))

    main | no ¬p | boxInterpBiobs eq1 .(multisubst' 0 γ1 t1) .(multisubst' 0 γ2 t1) inner1 | boxInterpBiobs eq2 .(multisubst' 0 γ1 (Promote t2)) .(multisubst' 0 γ2 (Promote t2)) inner2 =
      ⊥-elim (¬p (partialJoinMono eq1 eq2 gj (partialJoinIdem {adv})))

    main | no ¬p | left | right =
      boxInterpBiunobs ¬p (multisubst' zero γ1 (App t1 t2)) (multisubst' zero γ2 (App t1 t2)) ((obsMain1 , obsMain2))
        where
          leftb  : ⟦ Box g1 (FunTy A r B) ⟧v adv (Promote (multisubst' 0 γ1 t1)) (Promote (multisubst' 0 γ2 t1))
          leftb = biFundamentalTheoremGhost' {sz} {Γ1} {g1} {t1} {FunTy A r B} typ1 {γ1} {γ2} adv (splitContext1 contextInterp)

          rightb  : ⟦ Box (r *R g2) (Box r A) ⟧v adv (Promote (multisubst' 0 γ1 (Promote t2))) (Promote (multisubst' 0 γ2 (Promote t2)))
          rightb = biFundamentalTheoremGhost' {sz} {r · Γ2} {r *R g2} {Promote t2} {Box r A} (pr {Γ' = (r · Γ2 , r *R g2)} {r} typ2 {refl}) {γ1} {γ2} adv (splitContext2 contextInterp)

          inner1 : [ FunTy A r B ]e (multisubst' 0 γ1 t1) × [ FunTy A r B ]e (multisubst' 0 γ2 t1)
          inner1 with leftb
          ... | boxInterpBiobs _ .(multisubst' 0 γ1 t1) .(multisubst' 0 γ2 t1) inner =
                     binaryImpliesUnary { A = FunTy A r B } {multisubst γ1 t1} {multisubst γ2 t1} inner
          ... | boxInterpBiunobs _ .(multisubst' 0 γ1 t1) .(multisubst' 0 γ2 t1) (inner11 , inner12) =
                     (inner11 , inner12)

          inner2 : [ Box r A ]e (multisubst' 0 γ1 (Promote t2)) × [ Box r A ]e (multisubst' 0 γ2 (Promote t2))
          inner2 with rightb
          ... | boxInterpBiobs _ .(multisubst' 0 γ1 (Promote t2)) .(multisubst' 0 γ2 (Promote t2)) inner =
                     binaryImpliesUnary { A = Box r A } {multisubst γ1 (Promote t2)} {multisubst γ2 (Promote t2)} inner
          ... | boxInterpBiunobs _ .(multisubst' 0 γ1 (Promote t2)) .(multisubst' 0 γ2 (Promote t2)) (inner21 , inner22) =
                     (inner21 , inner22)

          obsMain1 : [ B ]e (multisubst' zero γ1 (App t1 t2))
          obsMain1 v1 v1redux  =
            let
              ((var1 , bod1) , (fun1redux , bodTy1)) = reduxTheoremAppTyG {multisubst' 0 γ1 t1} {multisubst' 0 γ1 t2} {v1} {0} {Empty} {A} {B} {r} {g1} (subst (\r -> multiRedux r ≡ v1) (substPresApp {0} {γ1} {t1} {t2}) v1redux) (multiSubstTyG {sz} {Γ1 , g1} {t1} {FunTy A r B} {γ1} typ1)
              fun1 = Abs var1 bod1

              ih1applied1 = (proj₁ inner1) fun1 fun1redux

              -- Join up the reductions
              -- multiRedux (App (multisubst' 0 γ1 t1) (multisubst' 0 γ1 t2)) ≡ v1
              aeq1 = trans (cong multiRedux (sym (substPresApp {0} {γ1} {t1} {t2}))) v1redux
              aeq2 = trans (sym (multReduxCongruence {multisubst' zero γ1 t1} {Abs var1 bod1} {\t1' -> App t1' (multisubst' 0 γ1 t2)} fun1redux)) aeq1
              v1reduxerFull = trans (sym (betaVariant1 {bod1} {multisubst' 0 γ1 t2} {var1})) aeq2

              -- Goal: [ Box r A ]e (Promote (multisubst γ1 t2))
              -- [ Box r A ]e (multisubst' 0 γ1 (Promote t2))
            in
              extractUn ih1applied1 (multisubst γ1 t2) (subst (\h -> [ Box r A ]e h) (substPresProm {0} {γ1} {t2}) (proj₁ inner2)) v1 v1reduxerFull

          obsMain2 : [ B ]e (multisubst' zero γ2 (App t1 t2))
          obsMain2 v2 v2redux =
            let
              ((var2 , bod2) , (fun2redux , bodTy2)) = reduxTheoremAppTyG {multisubst' 0 γ2 t1} {multisubst' 0 γ2 t2} {v2} {0} {Empty} {A} {B} {r} {g1} (subst (\r -> multiRedux r ≡ v2) (substPresApp {0} {γ2} {t1} {t2}) v2redux) (multiSubstTyG {sz} {Γ1 , g1} {t1} {FunTy A r B} {γ2} typ1)
              fun2 = Abs var2 bod2

              ih1applied2 = (proj₂ inner1) fun2 fun2redux

              -- Join up the reductions
              -- multiRedux (App (multisubst' 0 γ1 t1) (multisubst' 0 γ1 t2)) ≡ v1
              beq1 = trans (cong multiRedux (sym (substPresApp {0} {γ2} {t1} {t2}))) v2redux
              -- multiRedux (App (Abs var1 bod2) (multisubst' 0 γ2 t2)) ≡ v2
              beq2 = trans (sym (multReduxCongruence {multisubst' zero γ2 t1} {Abs var2 bod2} {\t1' -> App t1' (multisubst' 0 γ2 t2)} fun2redux)) beq1
              --
              v2reduxerFull = trans (sym (betaVariant1 {bod2} {multisubst' 0 γ2 t2} {var2})) beq2

            in
              extractUn ih1applied2 (multisubst γ2 t2) (subst (\h -> [ Box r A ]e h) (substPresProm {0} {γ2} {t2}) (proj₂ inner2)) v2 v2reduxerFull

biFundamentalTheoremGhost' {_} {_} {ghost} {.unit} {.Unit} unitConstr {γ1} {γ2} adv contextInterp rewrite substPresUnit {γ1} {0} | substPresUnit {γ2} {0} with 1R ≤d adv
... | yes p = boxInterpBiobs p unit unit inner
  where
    inner : ⟦ Unit ⟧e adv unit unit
    inner v1 v2 v1redux v2redux rewrite
        sym (trans (valuesDontReduce {unit} unitValue) v1redux)
      | sym (trans (valuesDontReduce {unit} unitValue) v2redux)
      = unitInterpBi

... | no ¬p =
     boxInterpBiunobs ¬p unit unit ( inner , inner )
  where
    inner : [ Unit ]e unit
    inner v vredux rewrite sym (trans (valuesDontReduce {unit} unitValue) vredux) = unitInterpV


-- # PROMOTION
biFundamentalTheoremGhost' {sz} {Γ'} {ghost} {Promote t} {Box r A} (pr {sz} {Γ} {Γ' , .ghost} {.r} typ {prf}) {γ1} {γ2} adv contextInterp rewrite prf with r ≤d adv | ghost ≤d adv
... | no ¬req | yes geq = boxInterpBiobs geq (multisubst γ1 (Promote t)) (multisubst γ2 (Promote t)) conclusion
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

    conclusion : ⟦ Box r A ⟧e adv (multisubst' 0 γ1 (Promote t)) (multisubst' 0 γ2 (Promote t))
    conclusion = {!let ih1 = utheorem {sz} {γ1} {?} {t} {A} typ in ?!}
     {- let
	(uinterp1 , uinterp2) = underBox {sz} {γ1} {γ2} {Γ} contextInterp
	ih1 = utheorem {s} {γ1} {Γ} {t} {A} typ uinterp1
	ih2 = utheorem {s} {γ2} {Γ} {t} {A} typ uinterp2
      in ? -}


... | no ¬req | no ¬geq = {!!}

... | yes eq | yes geq =   {!!}

... | yes eq | no ¬geq =   {!!}






biFundamentalTheoremGhost' {sz} {Γ} {e} {τ} typ {γ1} {γ2} adv contextInterp = {!!}

{-
-- # IDEA 2
{-# TERMINATING #-}
biFundamentalTheoremGhost2 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2
        -> ⟦ τ ⟧e (ghost *R adv) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost2 {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | (injPair2 pos) | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc
  where
    conc : ⟦ τ ⟧v (1R *R adv) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs   eq .a1 .a2 inner
      rewrite leftUnit* {adv} =
          inner v1 v2 (isSimultaneous' {v1} {a1} {γ1'} v1redux) (isSimultaneous' {v2} {a2} {γ2'} v2redux)
    -- problematic here as we cannot connect the unobservability of the output to the input
    ... | boxInterpBiunobs eq .a1 .a2 inner rewrite leftUnit* {adv} = {!!}


-- gen for any variable
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost2 {sz} {Γ} {ghost} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

-- # IDEA 2A
{-# TERMINATING #-}
biFundamentalTheoremGhost2a : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg (ghost # adv) γ1 γ2
        -> ⟦ τ ⟧e (ghost *R adv) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost2a {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | (injPair2 pos) | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc
  where
    conc : ⟦ τ ⟧v (1R *R adv) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs   eq .a1 .a2 inner
      rewrite leftUnit* {adv} =
          let z = inner v1 v2 (isSimultaneous' {v1} {a1} {γ1'} v1redux) (isSimultaneous' {v2} {a2} {γ2'} v2redux)
          -- I guess we can map ⟦ τ ⟧v 1 -> ⟦ τ ⟧v adv ...? as left could be more restricted than right?
          in {!!}
    -- problematic here as we cannot connect the unobservability of the output to the input
    -- ¬ (1 ≤ (1 # adv)
    --
    ... | boxInterpBiunobs eq .a1 .a2 inner rewrite leftUnit* {adv} =
      ⊥-elim (eq (subst (\h -> 1R ≤ h) (trans (sym (absorb# {R} {adv})) (comm# {R} {adv} {1R})) (reflexive≤ {1R}) ))

-- gen for any variable
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost2a {sz} {Γ} {ghost} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

{-# TERMINATING #-}
biFundamentalTheoremGhost2b : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg (ghost *R adv) γ1 γ2
        -> ⟦ τ ⟧e (ghost *R adv) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost2b {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | (injPair2 pos) | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc
  where
    conc : ⟦ τ ⟧v (1R *R adv) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs   eq .a1 .a2 inner
      rewrite leftUnit* {adv} =
          let z = inner v1 v2 (isSimultaneous' {v1} {a1} {γ1'} v1redux) (isSimultaneous' {v2} {a2} {γ2'} v2redux)
          -- I guess we can map ⟦ τ ⟧v 1 -> ⟦ τ ⟧v adv ...? as left could be more restricted than right?
          in z
    -- problematic here as we cannot connect the unobservability of the output to the input
    -- ¬ (1 ≤ (1 # adv)
    --
    ... | boxInterpBiunobs eq .a1 .a2 inner rewrite leftUnit* {adv} =
    -- NOPE
     {!!}
    --  ⊥-elim (eq (subst (\h -> 1R ≤ h) (trans (sym (absorb# {R} {adv})) (comm# {R} {adv} {1R})) (reflexive≤ {1R}) ))

-- gen for any variable
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost2b {sz} {Γ} {ghost} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}


-- # IDEA 3
{-# TERMINATING #-}
biFundamentalTheoremGhost3 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg (adv # ghost) γ1 γ2
        -> ⟦ τ ⟧e          (adv # ghost) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost3 {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | injPair2 pos | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as p```r`tosition in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where

    conc : ⟦ τ ⟧v (adv # 1R) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- inner     : ⟦ τ ⟧e ((R'' InformationFlowSemiring.# adv) 1R) a1 a2
    -- eq        : ghost ≤ adv # ghost
    -- goal      : ⟦ τ ⟧v adv v1 v2
    ... | boxInterpBiobs   eq .a1 .a2 inner =
        let eqa1 = isSimultaneous' {v1} {a1} {γ1'} v1redux
            eqa2 = isSimultaneous' {v2} {a2} {γ2'} v2redux
        in inner v1 v2 eqa1 eqa2
        -- eq : ¬ (1 ≤ (adv # 1r))
        --ghost = 1
    ... | boxInterpBiunobs eq .a1 .a2 inner =
      ⊥-elim (eq (subst (\h -> 1R ≤ h) (sym (absorb# {R} {adv})) (reflexive≤ {1R})))

-- var generalisation here
... | _ | _ | _ | _ = {!!}

biFundamentalTheoremGhost3 {_} {Γ} {ghost} {e} {τ} typing {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}


-- BAD because it requires 1 # adv = adv which is patently false.
biFundamentalTheoremGhost4 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg (adv # ghost) γ1 γ2
        -> ⟦ τ ⟧e          adv (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost4 {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | injPair2 pos | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as p```r`tosition in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where

    conc : ⟦ τ ⟧v adv v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- inner     : ⟦ τ ⟧e ((R'' InformationFlowSemiring.# adv) 1R) a1 a2
    -- eq        : ghost ≤ adv # ghost
    -- goal      : ⟦ τ ⟧v adv v1 v2
    ... | boxInterpBiobs   eq .a1 .a2 inner =
        let eqa1 = isSimultaneous' {v1} {a1} {γ1'} v1redux
            eqa2 = isSimultaneous' {v2} {a2} {γ2'} v2redux
        in {!!} -- inner v1 v2 eqa1 eqa2 -- UHOH requires 1 # adv = adv  which is false
        -- eq : ¬ (1 ≤ (adv # 1r))
        --ghost = 1
    ... | boxInterpBiunobs eq .a1 .a2 inner =
      ⊥-elim (eq (subst (\h -> 1R ≤ h) (sym (absorb# {R} {adv})) (reflexive≤ {1R})))

-- var generalisation here
... | _ | _ | _ | _ = {!!}

biFundamentalTheoremGhost4 {_} {Γ} {ghost} {e} {τ} typing {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}


biFundamentalTheoremGhost5 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , adv # ghost ⟧Γg adv γ1 γ2
        -> ⟦ τ ⟧e                (adv # ghost) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost5 {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | injPair2 pos | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as p```r`tosition in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where
    convertor : {A : Type} -> ⟦ A ⟧v adv v1 v2 -> ⟦ A ⟧v 1R v1 v2
    convertor {FunTy A r A₁} (funInterpBi e1 e2 x x₁ x₂) = {!!}
    convertor {Unit} unitInterpBi = unitInterpBi
    convertor {Box r A} (boxInterpBiobs preq t1 t2 inner) = {!!}
    convertor {Box r A} (boxInterpBiunobs x t1 t2 x₁) = {!!}
    convertor {BoolTy} boolInterpTrueBi = {!!}
    convertor {BoolTy} boolInterpFalseBi = {!!}

    conc : ⟦ τ ⟧v (adv # 1R) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- inner     : ⟦ τ ⟧e ((R'' InformationFlowSemiring.# adv) 1R) a1 a2
    -- eq        : ghost ≤ adv # ghost
    -- goal      : ⟦ τ ⟧v adv v1 v2
    ... | boxInterpBiobs   eq .a1 .a2 inner =
        let eqa1 = isSimultaneous' {v1} {a1} {γ1'} v1redux
            eqa2 = isSimultaneous' {v2} {a2} {γ2'} v2redux
        in {!!} -- inner v1 v2 eqa1 eqa2 -- UHOH requires 1 # adv = adv  which is false
        -- eq : ¬ (1 ≤ (adv # 1r))
        --ghost = 1
    ... | boxInterpBiunobs eq .a1 .a2 inner = {!!}
      -- ⊥-elim (eq (subst (\h -> 1R ≤ h) (sym (absorb# {R} {adv})) (reflexive≤ {1R})))

-- var generalisation here
... | _ | _ | _ | _ = {!!}

biFundamentalTheoremGhost5 {_} {Γ} {ghost} {e} {τ} typing {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}
-}

informationContextBuilder : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
  {r s adv : grade} -> r ≤ s -> r ≢ s -> InfoContext (s *R default) (r # (s *R default))
informationContextBuilder {r} {s} {adv} pre neg with  s ≤d r
informationContextBuilder {r} {s} {adv} pre neg | yes p = ⊥-elim (neg (antisymmetry pre p))
informationContextBuilder {r} {s} {adv} pre neg | no ¬p with (s *R default) ≤d (r # (s *R default))
informationContextBuilder {r = r} {s} {adv} pre neg | no ¬p | yes p = Visible p
informationContextBuilder {r = r} {s} {adv} pre neg | no ¬p | no ¬p₁ = Invisible ¬p₁

informationContextBuilder' : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
  {r s : grade} -> InfoContext (s *R default) (r # (s *R default))
informationContextBuilder' {r} {s} with (s *R default) ≤d (r # (s *R default))
... | yes p = Visible p
... | no ¬p = Invisible ¬p

{-
-- Non-interference result for the ghost calculus
nonInterferenceGhost :
   {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
   {e : Term} {r s : grade} {pre : r ≤ s} {nonEq : r ≢ s}
        -> (Ext Empty (Grad BoolTy s) , r) ⊢ e ∶ Box r BoolTy

        -> (v1 v2 : Term)
        -> (Empty , default) ⊢ v1 ∶ BoolTy
        -> (Empty , default) ⊢ v2 ∶ BoolTy
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) == multiRedux (syntacticSubst v2 0 e)

nonInterferenceGhost {{R}} {{R'}} {{R''}} {e} {r} {s} {pre} {nonEq} typing v1 v2 v1typing v2typing isvalv1 isvalv2 with
    -- we can think of r as the adversary

    -- Apply fundamental binary theorem to v1
    biFundamentalTheoremGhost5 {zero} {Empty} {s *R default} {Promote v1} {Box s BoolTy}
    --  Invisible {s *R default} {r} {!trans pre (sym (unit# {s})) !}
    -- InfoContext
    --  ((R Semiring.*R s) (InformationFlowSemiring.default R''))
    --  ((R'' InformationFlowSemiring.# r)
    --   ((R Semiring.*R s) (InformationFlowSemiring.default R''))

-- informationContextBuilder' {r} {s}
                  (pr {_} {(Empty , default)} {Empty , s *R default} {s} {BoolTy} {v1} v1typing {refl}) {[]} {[]} r (tt , {!!}) (Promote v1) (Promote v1)
                  (valuesDontReduce {Promote v1} (promoteValue v1))
                  (valuesDontReduce {Promote v1} (promoteValue v1))
    -- Apply fundamental binary theorem to v2
  | biFundamentalTheoremGhost5 {zero} {Empty} {s *R default} {Promote v2} {Box s BoolTy}
                  (pr {_} {(Empty , default )} {Empty , s *R default} {s} {BoolTy} {v2} v2typing {refl})  {[]} {[]} r (tt , {!!}) (Promote v2) (Promote v2)
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  -- goal : s ≤ r
                  -- pre : r ≤ s
                  -- pre1 : s ≤ (r # (s * default))
... | boxInterpBiobs pre1 .v1 .v1 inner1 |  boxInterpBiobs pre2 .v2 .v2 inner2 = ⊥-elim ((nonEq (antisymmetry pre {!!}))) --(nonEq (antisymmetry pre {!!}))
... | boxInterpBiobs pre1 .v1 .v1 inner1 | boxInterpBiunobs pre2 .v2 .v2 inner2 = ⊥-elim (⊥-elim (pre2 pre1))
... | boxInterpBiunobs pre1 .v1 .v1 inner1 | boxInterpBiobs pre2 .v2 .v2 inner2 = ⊥-elim (⊥-elim (pre1 pre2))
... | boxInterpBiunobs pre1 .v1 .v1 (valv1 , valv1') | boxInterpBiunobs pre2 .v2 .v2 (valv2 , valv2') =
 let
   -- Show that substituting v1 and evaluating yields a value
   -- and since it is a graded modal type then this value is necessarily
   -- of the form Promote v1''
   substTy1 = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v1typing
   (v1'' , prf1) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} {Empty} {Box r BoolTy} {syntacticSubst v1 0 e} substTy1) (multiReduxProducesValuesG substTy1)

   -- ... same as above but for v2 ... leading to result of Promote v2''
   substTy2  = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v2typing
   (v2'' , prf2) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} substTy2) (multiReduxProducesValuesG substTy2)

   -- Apply fundamental binary theorem on the result with the values coming from syntacitcally substituting
   -- then evaluating
   inner' = subst (\h -> ⟦ Box s BoolTy ⟧e h (Promote v1) (Promote v2)) (sym (idem# {R} {r})) (inner valv1' valv2')
--   res = biFundamentalTheoremGhost5 {1} {Ext Empty (Grad BoolTy s)} {r} {e} {Box r BoolTy} typing {v1 ∷ []} {v2 ∷ []} r
--          ((inner' , tt) , Visible {r} {r # r} (subst (\h -> r ≤ h) (sym (idem# {R} {r})) reflexive≤)) (Promote v1'') (Promote v2'') prf1 prf2
   res = biFundamentalTheoremGhost5 {1} {Ext Empty (Grad BoolTy s)} {r} {e} {Box r BoolTy} typing {v1 ∷ []} {v2 ∷ []} r
          ((inner valv1' valv2' , tt) , Visible {r # r} {r} (subst (\h -> h ≤ r) (sym (idem# {R} {r})) reflexive≤)) (Promote v1'') (Promote v2'') prf1 prf2


   -- Boolean typed (low) values are equal inside the binary interepration
   res' = subst (\h -> ⟦ Box r BoolTy ⟧v h (Promote v1'') (Promote v2'')) (idem# {R} {r}) res
   boolTyEq = boolBinaryExprInterpEquality v1'' v2'' (unpack res') -- res

   -- Plug together the equalities
     -- Promote
   eq = PromoteEq {v1''} {v2''} (embedReduxCong {v1''} {v2''} boolTyEq)
   eq2 = transFullBetaEq (embedEq prf1) eq

 in transFullBetaEq eq2 (embedEq (sym prf2))
   where

     inner : [ BoolTy ]e v1 -> [ BoolTy ]e v2 -> ⟦ Box s BoolTy ⟧e r (Promote v1) (Promote v2)
     inner av1 av2 v3 v4 v3redux v4redux
       rewrite trans (sym v3redux) (valuesDontReduce {Promote v1} (promoteValue v1))
             | trans (sym v4redux) (valuesDontReduce {Promote v2} (promoteValue v2)) =
       boxInterpBiunobs (antisymmetryAlt {R} {R'} {r} {s} pre nonEq) v1 v2 (av1 , av2)

     -- Helper to unpack interpretation type
     unpack : {v1 v2 : Term} -> ⟦ Box r BoolTy ⟧v r (Promote v1) (Promote v2) -> ⟦ BoolTy ⟧e r v1 v2
     unpack {v1} {v2} (boxInterpBiobs _ .v1 .v2 innerExprInterp) = innerExprInterp
     unpack {v1} {v2} (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = ⊥-elim (eq (reflexive≤ {r}))
-}

-- Non-interference result for the ghost calculus
nonInterferenceGhost1 :
   {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
   {e : Term} {r s : grade} {pre : r ≤ s} {nonEq : r ≢ s}
        -> (Ext Empty (Grad BoolTy s) , r) ⊢ e ∶ Box r BoolTy

        -> (v1 v2 : Term)
        -> (Empty , default) ⊢ v1 ∶ BoolTy
        -> (Empty , default) ⊢ v2 ∶ BoolTy
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) == multiRedux (syntacticSubst v2 0 e)

nonInterferenceGhost1 {{R}} {{R'}} {{R''}} {e} {r} {s} {pre} {nonEq} typing v1 v2 v1typing v2typing isvalv1 isvalv2 with
    -- we can think of r as the adversary

    -- Apply fundamental binary theorem to v1
    biFundamentalTheoremGhost' {zero} {Empty} {s *R default} {Promote v1} {Box s BoolTy}
                  (pr {_} {(Empty , default)} {Empty , s *R default} {s} {BoolTy} {v1} v1typing {refl}) {[]} {[]} r tt
    -- Apply fundamental binary theorem to v2
  | biFundamentalTheoremGhost' {zero} {Empty} {s *R default} {Promote v2} {Box s BoolTy}
                  (pr {_} {(Empty , default )} {Empty , s *R default} {s} {BoolTy} {v2} v2typing {refl})  {[]} {[]} r tt
                  -- goal : s ≤ r
                  -- pre : r ≤ s
                  -- pre1 : s ≤ (r # (s * default))

-- Issue appears to be if r = Dunno and s = Private
-- i.e., we want to take
--
--        Empty, default |- v1 : BoolTy
--        -----------------------------------------
--        Empty, s * default |- [v1] : [] s BoolTy
--
--        Private * default = default (of course because Private = 1)
--
--        Empty, default |- v1 : BoolTy
--        -----------------------------------------
--        Empty, default |- [v1] : [] Private BoolTy

--        but biFundamentalTheorem' puts a ghost on the output so when we are really considering
--        (s  * default) <= r here

--        [] (s * default) ([] Private BoolTy)

--        so perhaps we need to unpeel another later...

--        which in this tricky case case is Dunno <= Dunno which is true - but this only means we can see down to the
--        boxing underneath...
--
--         but we have that ¬ (Private <= Dunno) so this should be unobservable here.. what am I missing?


... | boxInterpBiobs pre1 (Promote .v1) (Promote .v1) inner1 | boxInterpBiobs pre2 (Promote .v2) (Promote .v2) inner2 =
  ⊥-elim notPossible
  where
    notPossible : ⊥
    notPossible with inner1 (Promote v1) (Promote v1) refl refl | inner2 (Promote v2) (Promote v2) refl refl
    ... | boxInterpBiobs   prei1 .v1 .v1 inneri1 | _ = ⊥-elim (antisymmetryAlt {R} {R'} pre nonEq prei1)
    ... | boxInterpBiunobs prei1 .v1 .v1 inneri1 | boxInterpBiobs   prei2 .v2 .v2 inneri2 = ⊥-elim (antisymmetryAlt {R} {R'} pre nonEq prei2)

--- maybe this okay though and we can work from here similar to the one below....(a bit like old proof)
    ... | boxInterpBiunobs prei1 .v1 .v1 inneri1 | boxInterpBiunobs prei2 .v2 .v2 inneri2 = {!!}

  -- ⊥-elim ((nonEq (antisymmetry pre {!!}))) --(nonEq (antisymmetry pre {!!}))
... | boxInterpBiobs pre1 (Promote .v1) (Promote .v1) inner1 | boxInterpBiunobs pre2 (Promote .v2) (Promote .v2) inner2 = ⊥-elim (⊥-elim (pre2 pre1))
... | boxInterpBiunobs pre1 (Promote .v1) (Promote .v1) inner1 | boxInterpBiobs pre2 (Promote .v2) (Promote .v2) inner2 = ⊥-elim (⊥-elim (pre1 pre2))
... | boxInterpBiunobs pre1 (Promote .v1) (Promote .v1) (valv1 , valv1') | boxInterpBiunobs pre2 (Promote .v2) (Promote .v2) (valv2 , valv2') =
 let
   -- Show that substituting v1 and evaluating yields a value
   -- and since it is a graded modal type then this value is necessarily
   -- of the form Promote v1''
   substTy1 = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v1typing
   (v1'' , prf1) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} {Empty} {Box r BoolTy} {syntacticSubst v1 0 e} substTy1) (multiReduxProducesValuesG substTy1)

   -- ... same as above but for v2 ... leading to result of Promote v2''
   substTy2  = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v2typing
   (v2'' , prf2) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} substTy2) (multiReduxProducesValuesG substTy2)

   -- Apply fundamental binary theorem on the result with the values coming from syntacitcally substituting
   -- then evaluating
   res = biFundamentalTheoremGhost' {1} {Ext Empty (Grad BoolTy s)} {r} {e} {Box r BoolTy} typing {v1 ∷ []} {v2 ∷ []} r
          (inner (extr valv1') (extr valv2') , tt)

   -- unpack the result based on the reducability up to promotion
   res' = unpack (unpack res (Promote v1'') (Promote v2'') prf1 prf2)
   boolTyEq = boolBinaryExprInterpEquality v1'' v2'' res'

   -- Plug together the equalities
     -- Promote
   eq = PromoteEq {v1''} {v2''} (embedReduxCong {v1''} {v2''} boolTyEq)
   eq2 = transFullBetaEq (embedEq prf1) eq

 in transFullBetaEq eq2 (embedEq (sym prf2))
   where
     extr : {v1 : Term} -> [ Box s BoolTy ]e (Promote v1) -> [ BoolTy ]e v1
     extr {v1} pre v redux with pre (Promote v1) refl
     ... | boxInterpV .v1 inner' =  let k = inner' v redux in k

     inner : [ BoolTy ]e v1 -> [ BoolTy ]e v2 -> ⟦ Box s BoolTy ⟧e r (Promote v1) (Promote v2)
     inner av1 av2 v3 v4 v3redux v4redux
       rewrite trans (sym v3redux) (valuesDontReduce {Promote v1} (promoteValue v1))
             | trans (sym v4redux) (valuesDontReduce {Promote v2} (promoteValue v2)) =
       boxInterpBiunobs (antisymmetryAlt {R} {R'} {r} {s} pre nonEq) v1 v2 (av1 , av2)

     -- Helper to unpack interpretation type
     unpack : {v1 v2 : Term} {A : Type} -> ⟦ Box r A ⟧v r (Promote v1) (Promote v2) -> ⟦ A ⟧e r v1 v2
     unpack {v1} {v2} (boxInterpBiobs _ .v1 .v2 innerExprInterp) = innerExprInterp
     unpack {v1} {v2} (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = ⊥-elim (eq (reflexive≤ {r}))
