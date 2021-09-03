{-# OPTIONS --allow-unsolved-metas #-}

module RelationalModelGhostAlt where

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

-- Contexts

-- unary
-- [_]Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> List Term -> Set
-- [ (Γ , ghostGrade) ]Γg γ = [ Γ ]Γ γ

-- binary
data ⟦_⟧Γg {{R : Semiring}} : {s : ℕ} -> ContextG s -> (adv : grade) -> List Term -> List Term -> Set where
    visible : {sz : ℕ} {Γ : Context sz} {ghost adv : grade} {γ1 γ2 : List Term}
            -> ghost ≤ adv -> ⟦ Γ ⟧Γ adv γ1 γ2 -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2

    invisible : {sz : ℕ} {Γ : Context sz} {ghost adv : grade} {γ1 γ2 : List Term}
            -> ¬ (ghost ≤ adv) -> [ Γ ]Γ γ1 × [ Γ ]Γ γ2 -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2


injPair1 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> a ≡ a'
injPair1 refl = refl

injPair2 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> b ≡ b'
injPair2 refl = refl

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

extractUn : {{R : Semiring}} {r : grade} {A : Type} {v : Term} -> [ Box r A ]e (Promote v) -> [ A ]e v
extractUn {r} {A} {v} ab v1 v1redux with ab (Promote v) refl
... | boxInterpV _ inner = inner v1 v1redux

utheoremG : {{R : Semiring}} {{R' : InformationFlowSemiring R}} {s : ℕ} {γ : List Term}
        -> {Γ : Context s} {ghost : grade} {e : Term} {τ : Type}
        -> (Γ , ghost) ⊢ e ∶ τ
        -> [ Γ ]Γ γ
        -> [ τ ]e (multisubst γ e)
utheoremG = {!!}

multireduxPromoteLemma :
  {{ R : Semiring }}
  {adv r : grade}
  {τ : Type}
  {t1 t2 : Term}
  -> ⟦ Box r τ ⟧e adv t1 t2
  -> Σ (Term × Term) (\(v1 , v2) -> multiRedux t1 ≡ Promote v1 × multiRedux t2 ≡ Promote v2)
multireduxPromoteLemma = {!!}

-- under some constraints perhaps
--unaryImpliesBinarySpecialised : {e : Term} {τ : Type}
--  ⟦ τ ⟧e t

sameContext : {{R : Semiring}}
              {sz : ℕ} {Γ : Context sz}
              {s adv : grade}
              {γ1 γ2 : List Term}
            -> ⟦ s · Γ ⟧Γ adv γ1 γ2
            -> (s ≤ adv)
            -> γ1 ≡ γ2
sameContext ⦃ R ⦄ {.0} {Empty} {s} {adv} {[]} {[]} ctxt pre = refl
sameContext ⦃ R ⦄ {.(suc _)} {Ext Γ x} {s} {adv} {[]} {[]} ctxt pre = refl
sameContext ⦃ R ⦄ {.(suc _)} {Ext Γ (Grad A r)} {s} {adv} {[]} {x₁ ∷ γ2} () pre
sameContext ⦃ R ⦄ {.(suc _)} {Ext Γ (Grad A r)} {s} {adv} {x₁ ∷ γ1} {[]} () pre
sameContext ⦃ R ⦄ {.(suc _)} {Ext Γ (Grad A r)} {s} {adv} {x₁ ∷ γ1} {x₂ ∷ γ2} (ctxtHd , ctxtTl) pre
 with s · (Ext Γ (Grad A r)) | ctxtHd (Promote x₁) (Promote x₂) refl refl
... | Ext sΓ (Grad A' sr) | boxInterpBiobs pre2 .x₁ .x₂ inner = {!!}
... | Ext sΓ (Grad A' sr) | boxInterpBiunobs pre2 .x₁ .x₂ inner = {!!}

equalUnderSubst : {{R : Semiring}}
              {sz : ℕ} {Γ : Context sz} {e : Term} {τ : Type}
              {s adv : grade}
              {γ1 γ2 : List Term}
            -> ⟦ s · Γ ⟧Γ adv γ1 γ2
            -> Γ ⊢ e ∶ τ
            -> (s ≤ adv)
            -> multisubst γ1 e ≡ multisubst γ2 e
equalUnderSubst = ?


delta : {{R : Semiring}}
        {adv r s : grade}
        {t1 t2 : Term}
        {τ : Type}
      -> ⟦ Box (s *R r) τ ⟧e adv t1 t2
      -> ⟦ Box s (Box r τ) ⟧e adv t1 t2
delta {{R}} {adv} {r} {s} {t1} {t2} {τ} inp v1 v2 v1redux v2redux with s ≤d adv | r ≤d adv | (s *R r) ≤d adv
... | yes p1 | yes p2 | yes p3 = {!boxInterpBiobs!}
... | yes p1 | yes p2 | no ¬p3 = {!!}
... | yes p1 | no ¬p2 | yes p3 = {!!}
... | yes p1 | no ¬p2 | no ¬p3 = {!!}
... | no ¬p1 | yes p2 | yes p3 = {!!}
... | no ¬p1 | yes p2 | no ¬p3 = {!!}
... | no ¬p1 | no ¬p2 | yes p3 = {!!}
... | no ¬p1 | no ¬p2 | no ¬p3 = {!!}

intermediate : {{R : Semiring}} {sz : ℕ}
            {Γ : Context sz}
            {ghost s adv : grade}
            {γ1 γ2 : List Term}
            {τ : Type}
            {e : Term}
            -> ⟦ s · Γ ⟧Γ adv γ1 γ2
            -> (s ≤ adv)
            -> ⟦ Box ghost τ ⟧v adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))
            -> ¬ (ghost ≤ adv)
            -> ⟦ Box (ghost *R s) τ ⟧v adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))
intermediate {{R}} {Γ} {sz} {ghost} {s} {adv} {γ1} {γ2} {τ} {e} inp pre1 inner pre2
 with (ghost *R s) ≤d adv
{-
  But what if s = Public, g = Private, adv = Public
  then we have s ≤ adv (Public ≤ Public) yes
             ¬ (ghost ≤ adv) meaning ¬ (Private ≤ Public) yes
             (ghost *R s) = Public * Private = Public
        therefore (ghost *R s) ≤ Public is Public ≤ Public which is true.
 therefore adversary cannot see inside Box ghost τ but should be able to see inside Box (ghost *R s).
-}
intermediate {{R}} {sz} {Γ} {ghost} {s} {adv} {γ1} {γ2} {τ} {e} inp pre1 inner pre2 | yes p with inner
intermediate ⦃ R ⦄ {sz} {Γ} {ghost} {s} {adv} {γ1} {γ2} {τ} {e} inp pre1 inner pre2
  | yes p | boxInterpBiobs x .(multisubst' 0 γ1 e) .(multisubst' 0 γ2 e) inner' =
    boxInterpBiobs p (multisubst' zero γ1 e) (multisubst' zero γ2 e) inner'
intermediate ⦃ R ⦄ {sz} {Γ} {ghost} {s} {adv} {γ1} {γ2} {τ} {e} inp pre1 inner pre2
  | yes p | boxInterpBiunobs x .(multisubst' 0 γ1 e) .(multisubst' 0 γ2 e) inner' =
    boxInterpBiobs p (multisubst' zero γ1 e) (multisubst' zero γ2 e) (innerNew inp)
    where
      innerNew : {Γ : Context sz} -> ⟦ s · Γ ⟧Γ adv γ1 γ2 -> ⟦ τ ⟧e adv (multisubst' zero γ1 e) (multisubst' zero γ2 e)
      innerNew {Γ} inp with Γ | inp
      ... | Empty | ctxtInterp = {!!}
      ... | Ext ctx x | ctxinterp = {!!}

intermediate {{R}} {Γ} {sz} {ghost} {s} {adv} {γ1} {γ2} {τ} {e} inp pre1 inner pre2 | no ¬p = {!!}


biFundamentalTheoremGhost : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ (Γ , ghost) ⟧Γg adv γ1 γ2
        -> ⟦ Box ghost τ ⟧v adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))
        -- another idea is `Box 1 τ` here

biFundamentalTheoremGhost {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp
 rewrite injPair1 pos | sym (injPair2 pos) with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as position in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | visible eq (argInterp , restInterp) = conc

  where
    conc : ⟦ Box ghost τ ⟧v adv (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- goal : ghost ≤ adv
    -- eq   : 1 ≤ adv
    ... | boxInterpBiobs   eq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiobs eq a1 a2 inner

    ... | boxInterpBiunobs neq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          ⊥-elim (neq eq)

... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | invisible neq ((argInterp1 , restInterp1) , (argInterp2 , restInterp2)) = conc
  where
    conc : ⟦ Box ghost τ ⟧v adv (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
    conc rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
      boxInterpBiunobs neq a1 a2 (extractUn argInterp1 , extractUn argInterp2)

-- var generalisation here
... | _ | _ | _ | _ = {!!}

biFundamentalTheoremGhost {sz} {Γ'} {ghost} {Promote t} {Box r A} (pr {sz} {Γ , ghost'} {Γ' , .ghost} {.r} typ {prf}) {γ1} {γ2} adv contextInterpG rewrite prf
  with contextInterpG
{-
  G, ghost g' |- t : A
------------------------------
  G, ghost g |- [t] : Box r A

 where g = r * g'

 model is then
   Box g ⟦ G ⟧ -> Box g (Box r ⟦ A ⟧)
-}
biFundamentalTheoremGhost {{R}} {sz} {Γ'} {ghost} {Promote t} {Box r A} (pr {sz} {Γ , ghost'} {Γ' , .ghost} {.r} typ {prf}) {γ1} {γ2} adv contextInterpG | visible eq0 contextInterp with r ≤d adv
... | yes eq rewrite injPair2 prf | idem* {R} {r} =
  let
    ih = biFundamentalTheoremGhost {sz} {Γ} {ghost'} {t} {A} typ {γ1} {γ2} adv {!!}
    ih0 = subst (\h -> ⟦ Box ghost' A ⟧v adv h (Promote (multisubst γ2 t)))
             (sym (substPresProm {zero} {γ1} {t})) ih
    ih1 = subst (\h -> ⟦ Box ghost' A ⟧v adv (multisubst γ1 (Promote t)) h)
             (sym (substPresProm {zero} {γ2} {t})) ih0
    az = intermediate {sz} {Γ} {ghost'} {r} {adv} {γ1} {γ2} {A} {Promote t} contextInterp eq {!ih!} {!!}
    az2 = congidm {multisubst' zero γ1 (Promote t)} {multisubst' zero γ2 (Promote t)} {!!}
  in
    {!z2!}


-- Previous implementation:
-- main
{-
  We now know that
  eq0 : g ≤ adv
  eq : r ≤ adv
  Therefore the adversary can observer under the box(es) down to the value of t
-}
  where
    congidm : {t1 t2 : Term} -> ⟦ Box (ghost' *R r) A ⟧v adv t1 t2 -> ⟦ Box (r *R ghost') (Box r A) ⟧v adv t1 t2
    congidm = {!!}

    main : ⟦ Box ghost (Box r A) ⟧v adv (Promote (multisubst' 0 γ1 (Promote t))) (Promote (multisubst' 0 γ2 (Promote t)))
    main rewrite injPair2 prf = boxInterpBiobs eq0 (multisubst γ1 (Promote t))  (multisubst γ2 (Promote t)) conclusion
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
        underBox {_} {[]} {[]} {Empty}   g = tt
        underBox {suc n} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A s)} (ass , g) = convertExp {s} {v1} {v2} {A} ass , underBox {n} {γ1} {γ2} {Γ} g
        underBox {_} {[]} {[]} {Ext Γ (Grad A r₁)} ()
        underBox {_} {[]} {x ∷ γ5} {Ext Γ (Grad A r₁)} ()
        underBox {_} {x ∷ γ4} {[]} {Ext Γ (Grad A r₁)} ()

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


        underBox2 : {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> [ Γ ]Γ γ1 × [ Γ ]Γ γ2
        underBox2 {_} {_} {_} {Empty} g = (tt , tt)
        underBox2 {_} {[]} {[]} {Ext Γ (Grad A r)} ()
        underBox2 {_} {[]} {x ∷ γ2} {Ext Γ (Grad A r)} ()
        underBox2 {_} {x ∷ γ1} {[]} {Ext Γ (Grad A r)} ()
        underBox2 {suc sz} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A r')} (arg , g) =
         let
          (left , right) = underBox2 {sz} {γ1} {γ2} {Γ} g
          (l , r) = binaryToUnaryExp arg
         in
           (l , left) , (r , right)

        conclusion : ⟦ Box r A ⟧e adv (multisubst' 0 γ1 (Promote t)) (multisubst' 0 γ2 (Promote t))
        conclusion v1 v2 v1redux v2redux rewrite injPair1 prf | sym (injPair2 prf) |  sym (reduxAndSubstCombinedProm {v1} {t} {γ1} v1redux) |  sym (reduxAndSubstCombinedProm {v2} {t} {γ2} v2redux) {- =
          let ih = biFundamentalTheoremGhost {sz} {Γ} {ghost'} {t} {A} typ {γ1} {γ2} adv (visible {!!} (underBox {sz} {γ1} {γ2} contextInterp))
          in boxInterpBiobs eq (multisubst' zero γ1 t) (multisubst' zero γ2 t) {!!} -}

          with ghost' ≤d adv
        ... | yes geq' =
           let ih = biFundamentalTheoremGhost {sz} {Γ} {ghost'} {t} {A} typ {γ1} {γ2} adv (visible geq' (underBox {sz} {γ1} {γ2} contextInterp))
           in boxInterpBiobs eq (multisubst' zero γ1 t) (multisubst' zero γ2 t) (unpackObs geq' ih)
        ... | no geq' rewrite sym (injPair2 prf) = {!!}

{-

-- (trans (monotone* {!!} {!!}) (idem* {adv}))
           -- eq : r ≤ adv
           --   i.e., the adversary can see inside the box (if ghosts are ignored)
           -- geq : r * ghost' ≤ adv
           --   i.e., the adversary can see inside the outer ghost box
           --  BUT
           -- geq' : ¬ (ghost' ≤ adv)
           --   i.e., the adversary cannot see inside the ghosted box

            let ih = biFundamentalTheoremGhost {sz} {Γ} {ghost'} {t} {A} typ {γ1} {γ2} adv (invisible geq' (underBox2 {sz} {γ1} {γ2} contextInterp))
                --ih0 = unpackObs {!!} ih
                ih' = (unpackUnobs geq' ih)
                in boxInterpBiobs eq (multisubst' zero γ1 t) (multisubst' zero γ2 t) {!!}
                --in boxInterpBiunobs {!!} (multisubst' zero γ1 t) (multisubst' zero γ2 t) ih' -- boxInterpBiobs {!!} (multisubst' zero γ1 t) (multisubst' zero γ2 t) ? (unpackUnobs geq' ih)

-}

... | no ¬req = main
  where
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

    main : ⟦ Box ghost (Box r A) ⟧v adv (Promote (multisubst' 0 γ1 (Promote t))) (Promote (multisubst' 0 γ2 (Promote t)))
    main with ghost ≤d adv
    ... | yes geq = boxInterpBiobs geq (multisubst γ1 (Promote t))  (multisubst γ2 (Promote t)) conclusion
      where

        conclusion : ⟦ Box r A ⟧e adv (multisubst' 0 γ1 (Promote t)) (multisubst' 0 γ2 (Promote t))
        conclusion v1 v2 v1redux v2redux rewrite injPair1 prf =

          let
            (uinterp1 , uinterp2) = underBox {sz} {γ1} {γ2} {Γ} contextInterp
            ih1 = utheoremG {sz} {γ1} {Γ} {ghost'} {t} {A} typ uinterp1
            ih2 = utheoremG {sz} {γ2} {Γ} {ghost'} {t} {A} typ uinterp2
            out = boxInterpBiunobs ¬req (multisubst γ1 t) (multisubst γ2 t) (ih1 , ih2)
          in subst₂ (\h1 h2 -> ⟦ Box r A ⟧v adv h1 h2)
            (reduxAndSubstCombinedProm {v1} {t} {γ1} v1redux)
            (reduxAndSubstCombinedProm {v2} {t} {γ2} v2redux) out

    ... | no ¬geq = boxInterpBiunobs ¬geq (multisubst γ1 (Promote t)) (multisubst γ2 (Promote t)) (conclusion1 , conclusion2)
      where
        conclusion1 : [ Box r A ]e (multisubst' 0 γ1 (Promote t))
        conclusion1 v1 v1redux rewrite injPair1 prf | sym (reduxAndSubstCombinedProm {v1} {t} {γ1} v1redux) =
          let
            (uinterp1 , uinterp2) = underBox {sz} {γ1} {γ2} {Γ} contextInterp
            ih1 = utheoremG {sz} {γ1} {Γ} {ghost'} {t} {A} typ uinterp1
          in boxInterpV (multisubst γ1 t) ih1

        conclusion2 : [ Box r A ]e (multisubst' 0 γ2 (Promote t))
        conclusion2 v2 v2redux rewrite injPair1 prf | sym (reduxAndSubstCombinedProm {v2} {t} {γ2} v2redux) =
          let
            (uinterp1 , uinterp2) = underBox {sz} {γ1} {γ2} {Γ} contextInterp
            ih2 = utheoremG {sz} {γ2} {Γ} {ghost'} {t} {A} typ uinterp2
          in boxInterpV (multisubst γ2 t) ih2


biFundamentalTheoremGhost {sz} {Γ'} {ghost} {Promote t} {Box r A} (pr {sz} {Γ , ghost'} {Γ' , .ghost} {.r} typ {prf}) {γ1} {γ2} adv contextInterpG | invisible neq (contextInterp1 , contextInterp2) with ghost ≤d adv
... | yes geq rewrite injPair2 prf = ⊥-elim (neq geq)


... | no ¬geq = boxInterpBiunobs ¬geq (multisubst' zero γ1 (Promote t)) (multisubst' zero γ2 (Promote t)) ((conclusion1 , conclusion2))
   where
        convert : {s : grade} {v : Term} {A : Type} -> [ Box (r *R s) A ]e (Promote v) -> [ Box s A ]e (Promote v)
        convert {s} {v} {A} pre v0 v0redux with pre v0 v0redux
        ... | boxInterpV e inner = boxInterpV e inner

        underBox : {sz : ℕ} {γ : List Term} {Γ : Context sz} -> [ r · Γ ]Γ γ -> [ Γ ]Γ γ
        underBox {0} {_} {Empty} g = tt
        underBox {suc sz} {v ∷ γ} {Ext Γ (Grad A s)} (ass , g) = convert ass , underBox {sz} {γ} {Γ} g

        conclusion1 : [ Box r A ]e (multisubst' 0 γ1 (Promote t))
        conclusion1 v1 v1redux rewrite injPair1 prf =
          let ih = utheoremG typ (underBox contextInterp1)
          in subst (\h -> [ Box r A ]v h) (reduxAndSubstCombinedProm {v1} {t} {γ1} v1redux) (boxInterpV (multisubst γ1 t) ih)

        conclusion2 : [ Box r A ]e (multisubst' 0 γ2 (Promote t))
        conclusion2 v2 v2redux rewrite injPair1 prf =
          let ih = utheoremG typ (underBox contextInterp2)
          in subst (\h -> [ Box r A ]v h) (reduxAndSubstCombinedProm {v2} {t} {γ2} v2redux) (boxInterpV (multisubst γ2 t) ih)

-- reduxAndSubstCombinedProm

biFundamentalTheoremGhost {sz} {Γ} {ghost} {t} {A} typ {γ1} {γ2} adv contextInterp = {!!}

biFundamentalTheoremGhost {sz} {Γ} {ghost} {t} {A} typ {γ1} {γ2} adv contextInterp = {!!}


nonInterferenceGhostAlt :
   {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
   {e : Term} {r s : grade} {pre : r ≤ s} {nonEq : r ≢ s}
        -> (Ext Empty (Grad BoolTy s) , r) ⊢ e ∶ Box r BoolTy

        -> (v1 v2 : Term)
        -> (Empty , default) ⊢ v1 ∶ BoolTy
        -> (Empty , default) ⊢ v2 ∶ BoolTy
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) == multiRedux (syntacticSubst v2 0 e)

nonInterferenceGhostAlt {{R}} {{R'}} {{R''}} {e} {r} {s} {pre} {nonEq} typing v1 v2 v1typing v2typing isvalv1 isvalv2 =
 {!!}
