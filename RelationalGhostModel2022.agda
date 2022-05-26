{-# OPTIONS --allow-unsolved-metas #-}

module RelationalGhostModel2022 where

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
  -- e.g., ¬ (Priv <= Pub)

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


biFundamentalTheoremGhost' : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ (Γ , ghost) ⟧Γg adv γ1 γ2
        -> ⟦ τ ⟧e (ghost # adv) (multisubst γ1 e) (multisubst γ2 e)


-- ---------------------------------------------- var
--    0G, Ghost_1, x :_1 A  |- x : A

-- 
-- 


biFundamentalTheoremGhost' {{R}} {{R'}} {{R''}} (var {A = τ} {_} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp e1 e2 e1redux e2redux rewrite injPair1 pos |  (injPair2 pos)  with Γ1 | γ1 | γ2 | contextInterp
... | Empty | v1 ∷ g1 | v2 ∷ g2 | (argInterp , _) , _ = conc
  where
    conc : ⟦ τ ⟧v (1R # adv) e1 e2
    -- 1R # adv = adv
    conc with argInterp (Promote v1) (Promote v2) refl refl
    ... | boxInterpBiobs x .v1 .v2 x₁ rewrite (oneIsKey {R} {adv}) = {!x₁ ? ? ? ?!}
    ... | boxInterpBiunobs x .v1 .v2 x₁ = {!!}
    
... | Ext g x | x₁ ∷ g1 | x₂ ∷ g2 | c = {!!}


... | Empty | [] | [] | c = {!!}
... | Ext g x | [] | [] | c = {!!}
... | Empty | [] | x ∷ g2 | c = {!!}
... | Ext g x | [] | x₁ ∷ g2 | c = {!!}
... | Empty | x ∷ g1 | [] | c = {!!}
... | Ext g x | x₁ ∷ g1 | [] | c = {!!}

biFundamentalTheoremGhost' (approx deriv approx1 approx2 sub) {γ1} {γ2} adv contextInterp = {!!}
biFundamentalTheoremGhost' (app deriv deriv₁) {γ1} {γ2} adv contextInterp = {!!}
biFundamentalTheoremGhost' (abs pos deriv) {γ1} {γ2} adv contextInterp = {!!}
biFundamentalTheoremGhost' (pr deriv) {γ1} {γ2} adv contextInterp = {!!}
biFundamentalTheoremGhost' unitConstr {γ1} {γ2} adv contextInterp = {!!}
biFundamentalTheoremGhost' trueConstr {γ1} {γ2} adv contextInterp = {!!}
biFundamentalTheoremGhost' falseConstr {γ1} {γ2} adv contextInterp = {!!}
biFundamentalTheoremGhost' (if deriv deriv₁ deriv₂) {γ1} {γ2} adv contextInterp = {!!}


biFundamentalTheoremGhost : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ (Γ , ghost) ⟧Γg adv γ1 γ2
        -> ⟦ τ ⟧e adv (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux
 rewrite injPair1 pos | sym (injPair2 pos) with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as position in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | (argInterp , restInterp) , Visible eq    = conc
   where
     conc : ⟦ τ ⟧v adv v1 v2
     conc with argInterp (Promote a1) (Promote a2) refl refl
     ... | boxInterpBiobs   eq .a1 .a2 inner = inner v1 v2 (isSimultaneous' {v1} {a1} {γ1'} v1redux) (isSimultaneous' {v2} {a2} {γ2'} v2redux)
     ... | boxInterpBiunobs neq .a1 .a2 inner = ⊥-elim (neq eq)


-- ----------------------------------------------
--    0G, Ghost_1, x :_1 A  |- x : A

... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | (argInterp , restInterp) , Invisible neq = conc
  where
    conc : ⟦ τ ⟧v adv v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs eq .a1 .a2 inner     = ⊥-elim (neq eq)
    ... | boxInterpBiunobs neq' .a1 .a2 inner = {!!}

{- conc

  where
     with ghostInterp
    ... | az = {!az!}
-}

-- var generalisation here
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost {sz} {Γ} {ghost} {t} {A} typ {γ1} {γ2} adv contextInterp = {!!}
