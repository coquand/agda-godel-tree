{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StageBase --
--
-- The BASE CASE  S(0)  of the external induction in T4/clos .
--
--   stageBase :
--     (consts : SurpriseConstsConj) ->
--     Lt (SurpriseConstsConj.M consts) (SurpriseConstsConj.N consts) ->
--     StagePred consts zero
--
-- Identical to T4.SurpriseG2.StageZeroNegsConj.descFamToNegs0
-- (pigeonhole on  ix d := progIx (family d) , determinism on the two
-- colliding ProgPacks at fuel  0 , numNeq + axExFalso) , except the
-- final  axExFalso  closes DIRECTLY to the day-independent target
-- eqF O (ap1 s O) ( = 0 = 1 ) -- no PerProgramNegConj detour because
-- StagePred outputs  Deriv 0=1  directly .

module T4.SurpriseG2.StageBase where

open import T4.Base
open import BRA3.RuleInst2                  using ( NatLe ; le-zero ; le-suc )
open import BRA3.Numerals                   using ( substT_natCode )
open import BRA3.Contrapositive             using ( axExFalso )
open import T4.Kdef                       using ( runProg )
open import T4.Thm12.ConstTermFun1        using ( NoVar ; NoVar_natCode )
open import T4.SubstNoVar                 using ( substT_NoVar )

open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.StagePred
  using ( ProgPack ; mkProgPack ; progIx ; ixBd ; runs
        ; DescribingFamily ; StagePred )
open import T4.SurpriseG2.Describes       using ( Describes )
open import T4.SurpriseG2.Determ          using ( runProg_det )
open import T4.SurpriseG2.NumNeq          using ( Not ; s_inj ; numNeq )
open import T4.SurpriseG2.MetaPigeonhole  as MP
  using ( Lt ; Collide ; pigeonhole )

------------------------------------------------------------------------
-- Top-level Lt / NatLe helpers ( with / where clauses not allowed
-- inside  let  bindings ) .

natLe_to_lt : (n m : Nat) -> NatLe m n -> Lt m (suc n)
natLe_to_lt n .zero (le-zero .n) = MP.ltZ n
natLe_to_lt (suc n') (suc m') (le-suc le') =
  MP.ltS m' (suc n') (natLe_to_lt n' m' le')

lt_to_natLe : (a b : Nat) -> Lt a (suc b) -> NatLe a b
lt_to_natLe zero    b     (MP.ltZ .b)              = le-zero b
lt_to_natLe (suc a) zero  (MP.ltS .a .zero h)      = MP.ltAbsurd h
lt_to_natLe (suc a) (suc b') (MP.ltS .a .(suc b') h) =
  le-suc (lt_to_natLe a b' h)

natLe_refl : (n : Nat) -> NatLe n n
natLe_refl zero    = le-zero zero
natLe_refl (suc n) = le-suc (natLe_refl n)

data NatLeDec (d N : Nat) : Set where
  natLeYes : NatLe d N -> NatLeDec d N
  natLeNo  : Lt N d   -> NatLeDec d N

natLeDecide : (d N : Nat) -> NatLeDec d N
natLeDecide d N with MP.natCmp d N
... | MP.ltC ltDN = natLeYes (lt_to_natLe d N (MP.ltWeaken ltDN))
... | MP.eqC eq   = natLeYes (eqSubst (\ z -> NatLe z N) (eqSym eq) (natLe_refl N))
... | MP.gtC ltND = natLeNo ltND

natLe_lt_contra : (a b : Nat) -> NatLe a b -> Lt b a -> Empty
natLe_lt_contra a b leAB ltBA =
  MP.ltIrrefl (MP.ltStrictTrans ltBA (natLe_to_lt b a leAB))

------------------------------------------------------------------------
-- Helper :  collapse the  substF  on a closed-enum  Describes  formula
-- under  ruleInst zero O .  ( Verbatim from StageZeroNegsConj .)

substF_collapse :
  (enum : Fun1) (progIx : Nat) (k : Nat) ->
  Deriv (substF zero O (Describes (ap1 enum (natCode progIx)) (natCode k))) ->
  Deriv (eqF (ap2 runProg (ap1 enum (natCode progIx)) O) (ap1 s (natCode k)))
substF_collapse enum progIx k d =
  let progT : Term
      progT = ap1 enum (natCode progIx)

      npT : NoVar progT
      npT = NoVar_natCode progIx

      eqP : Eq (substT zero O progT) progT
      eqP = substT_NoVar zero O progT npT

      eqNc : Eq (substT zero O (natCode k)) (natCode k)
      eqNc = substT_natCode zero O k

      d1 : Deriv (eqF (ap2 runProg progT O)
                       (ap1 s (substT zero O (natCode k))))
      d1 = eqSubst
             (\ p -> Deriv (eqF (ap2 runProg p O)
                                 (ap1 s (substT zero O (natCode k)))))
             eqP d

      d2 : Deriv (eqF (ap2 runProg progT O) (ap1 s (natCode k)))
      d2 = eqSubst
             (\ nc -> Deriv (eqF (ap2 runProg progT O) (ap1 s nc)))
             eqNc d1
  in d2

------------------------------------------------------------------------
-- Top-level pigeonhole inputs .   ix and getPack share the SAME
-- natLeDecide call so they reduce consistently .

module _ (consts : SurpriseConstsConj)
         (family : DescribingFamily consts zero) where

  private
    N = SurpriseConstsConj.N consts
    M = SurpriseConstsConj.M consts

  ixFun : Nat -> Nat
  ixFun d with natLeDecide d N
  ... | natLeYes le = progIx (family d (MP.ltZ d) le)
  ... | natLeNo  _  = zero

  bdFun : (i : Nat) -> Lt i (suc N) -> Lt (ixFun i) (suc M)
  bdFun i lti with natLeDecide i N
  ... | natLeYes le =
    natLe_to_lt M (progIx (family i (MP.ltZ i) le))
                  (ixBd (family i (MP.ltZ i) le))
  ... | natLeNo ltNI =
    emptyElim (MP.ltIrrefl (MP.ltStrictTrans ltNI lti))

  -- getPack at d , consistent with ixFun .   Given NatLe d N , the
  -- natLeDecide case picks SOME le' ;  this gives a valid ProgPack .
  getPack : (d : Nat) -> NatLe d N -> ProgPack consts d
  getPack d le with natLeDecide d N
  ... | natLeYes le' = family d (MP.ltZ d) le'
  ... | natLeNo  ltNd = emptyElim (natLe_lt_contra d N le ltNd)

  -- ix-pack-eq :  ixFun d  =  progIx (getPack d le)  for any d with NatLe d N .
  ixPackEq : (d : Nat) (le : NatLe d N) -> Eq (ixFun d) (progIx (getPack d le))
  ixPackEq d le with natLeDecide d N
  ... | natLeYes le' = refl
  ... | natLeNo  ltNd = emptyElim (natLe_lt_contra d N le ltNd)

------------------------------------------------------------------------
-- The base case  S(0) .

stageBase :
  (consts : SurpriseConstsConj) ->
  Lt (SurpriseConstsConj.M consts) (SurpriseConstsConj.N consts) ->
  StagePred consts zero
stageBase consts ltMN family =
  let open SurpriseConstsConj consts using ( N ; M ; enum )

      ix : Nat -> Nat
      ix = ixFun consts family

      bd : (i : Nat) -> Lt i (suc N) -> Lt (ix i) (suc M)
      bd = bdFun consts family

      coll : Collide ix N
      coll = pigeonhole ix N M bd ltMN

      i : Nat
      i = Collide.i_idx coll
      j : Nat
      j = Collide.j_idx coll
      i_lt_sN : Lt i (suc N)
      i_lt_sN = Collide.i_lt coll
      j_lt_sN : Lt j (suc N)
      j_lt_sN = Collide.j_lt coll
      i_neq_j : Not (Eq i j)
      i_neq_j = Collide.i_neq coll
      ix_i_eq_ix_j : Eq (ix i) (ix j)
      ix_i_eq_ix_j = Collide.ix_eq coll

      i_le_N : NatLe i N
      i_le_N = lt_to_natLe i N i_lt_sN

      j_le_N : NatLe j N
      j_le_N = lt_to_natLe j N j_lt_sN

      packI : ProgPack consts i
      packI = getPack consts family i i_le_N

      packJ : ProgPack consts j
      packJ = getPack consts family j j_le_N

      ixI : Nat
      ixI = progIx packI

      ixJ : Nat
      ixJ = progIx packJ

      -- Bridge :  ix i = ixI  and  ix j = ixJ ,  via ixPackEq .
      eqI : Eq (ix i) ixI
      eqI = ixPackEq consts family i i_le_N

      eqJ : Eq (ix j) ixJ
      eqJ = ixPackEq consts family j j_le_N

      ixI_eq_ixJ : Eq ixI ixJ
      ixI_eq_ixJ = eqTrans (eqSym eqI) (eqTrans ix_i_eq_ix_j eqJ)

      progI : Term
      progI = ap1 enum (natCode ixI)

      progJ : Term
      progJ = ap1 enum (natCode ixJ)

      sameProg : Eq progJ progI
      sameProg = eqSym (eqCong (\ n -> ap1 enum (natCode n)) ixI_eq_ixJ)

      runs_i : Deriv (Describes progI (natCode i))
      runs_i = runs packI

      runs_j : Deriv (Describes progJ (natCode j))
      runs_j = runs packJ

      runs_i_O : Deriv (eqF (ap2 runProg progI O) (ap1 s (natCode i)))
      runs_i_O = substF_collapse enum ixI i (ruleInst zero O runs_i)

      runs_j_O : Deriv (eqF (ap2 runProg progJ O) (ap1 s (natCode j)))
      runs_j_O = substF_collapse enum ixJ j (ruleInst zero O runs_j)

      runs_j_O_at_I :
        Deriv (eqF (ap2 runProg progI O) (ap1 s (natCode j)))
      runs_j_O_at_I =
        eqSubst (\ p -> Deriv (eqF (ap2 runProg p O) (ap1 s (natCode j))))
                 sameProg runs_j_O

      s_eq : Deriv (eqF (ap1 s (natCode i)) (ap1 s (natCode j)))
      s_eq = runProg_det progI O (natCode i) (natCode j)
               runs_i_O runs_j_O_at_I

      eq_nc : Deriv (eqF (natCode i) (natCode j))
      eq_nc = s_inj (natCode i) (natCode j) s_eq

      neg_eq : Deriv (neg (eqF (natCode i) (natCode j)))
      neg_eq = numNeq i j i_neq_j

      P : Formula
      P = eqF (natCode i) (natCode j)

      target : Formula
      target = eqF O (ap1 s O)
  in mp (mp (axExFalso P target) eq_nc) neg_eq
