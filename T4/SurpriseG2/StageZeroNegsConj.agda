{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.StageZeroNegsConj -- the day-0 per-prog negs at the
-- conjunction-shape K-formula reformulation (Residual A per
-- T4/NEXT-SESSION-CGICONJ-INSTANTIATE.md ).
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
--   descFamToNegs0 :
--     (consts : SurpriseConstsConj) ->
--     DescFamConj consts ->
--     PerProgramNegConj consts (natCode zero)
--
-- A parallel of the OLD  T4.SurpriseG2.StageZeroNegs.stageZeroNegs ,
-- producing the day-0 per-prog negs at the new shape :
--
--   (k : Nat) -> NatLe k M ->
--     Deriv (neg (definable (ap1 enum (natCode k)) (natCode zero) (var (suc zero)))) .
--
-- =====================================================================
-- HOW IT IS BUILT.
-- =====================================================================
--
--   1.   MetaPigeonhole.pigeonhole  on  (ix, N, M, ixBd, ltMN)  yields a
--        Collide ix N  --  two distinct days  i, j  with  ix i = ix j .
--   2.   Two  DescPackConj  records ( one per colliding day ) supply
--        Describes  derivations open over fuel  var 0 ,  each at program
--        ap1 enum (natCode progIx) .
--   3.   Inst  var 0 := O  in both ;   substT  collapses on  ap1 enum
--        (natCode progIx)  via   NoVar (natCode progIx)  =  NoVar_natCode
--        progIx .
--   4.   Rewrite  progJ -> progI  via the meta term-equality  Eq (ap1 enum
--        (natCode progIx_j)) (ap1 enum (natCode progIx_i))  ( from  ixEq
--        via  eqCong (ap1 enum o natCode) ) .
--   5.   Determinism  +  s-injectivity  +  numNeq  give the meta-Nat
--        contradiction  Deriv (eqF (natCode i) (natCode j))  /
--        Deriv (neg (eqF (natCode i) (natCode j))) .
--   6.   axExFalso  closes DIRECTLY to the per-prog neg target ( no
--        ConOpenInt / thmT detour -- the OLD  stageZero  used those
--        because it produced the bare seed  Deriv (eqF O (ap1 s O)) ;
--        here we ex-falso straight to whatever  k -indexed target
--        PerProgramNegConj  asks for ) .
--
-- =====================================================================
-- ON THE Sigma-VS-RECORD CHOICE  (per  feedback_specialised_record_typecheck_blowup ) .
-- =====================================================================
--
-- DescPackConj  is a  Sigma  alias  ( not a record ) :  its second
-- component is a  Deriv  field whose type mentions  ap1 enum (natCode
-- progIx)  which can trigger the dependent-field typecheck blowup when
-- the record is unfolded inside  stageZeroConj 's body .   The  Sigma
-- alias keeps the projection -- mkSigma  destructuring opaque to Agda's
-- record elaborator and the file warms in ~ 1s .
--
-- DescFamConj  is a record ( three independent fields ) ;  no  Deriv
-- field appears at the record level , only inside  descAt 's return
-- type , which is the  Sigma -aliased  DescPackConj .

module T4.SurpriseG2.StageZeroNegsConj where

open import T4.Base
open import BRA3.RuleInst2                  using ( NatLe ; le-zero ; le-suc )
open import BRA3.Numerals                   using ( substT_natCode )
open import BRA3.Contrapositive             using ( axExFalso )
open import T4.Kdef                       using ( runProg ; definable )
open import T4.Thm12.ConstTermFun1        using ( NoVar ; NoVar_natCode )
open import T4.SubstNoVar                 using ( substT_NoVar )

open import T4.SurpriseG2.ConstantsConj   using ( SurpriseConstsConj )
open import T4.SurpriseG2.KFormulaFromNegsConj
                                            using ( PerProgramNegConj )
open import T4.SurpriseG2.Describes       using ( Describes )
open import T4.SurpriseG2.Determ          using ( runProg_det )
open import T4.SurpriseG2.NumNeq          using ( Not ; s_inj ; numNeq )
open import T4.SurpriseG2.MetaPigeonhole  as MP
  using ( Lt ; Collide ; pigeonhole )
open import T4.SurpriseG2.CGIConjSpec     using ( Sigma ; mkSigma ; fst ; snd )

------------------------------------------------------------------------
-- DescPackConj  --  Sigma alias for a per-day description pack at the
-- new enumerator shape .
--
-- progIx : the chosen index in  [0..M]  ( the bound  Lt progIx (suc M)
-- is enforced by  DescFamConj.ixBd , NOT carried inside the pack ) .
--
-- runs   : the open-fuel  Describes  derivation , at program  ap1 enum
-- (natCode progIx) .

DescPackConj : SurpriseConstsConj -> Nat -> Set
DescPackConj consts k =
  let open SurpriseConstsConj consts using ( enum )
  in Sigma Nat (\ progIx ->
       Deriv (Describes (ap1 enum (natCode progIx)) (natCode k)))

-- Convenience projections .

dpcProgIx : (consts : SurpriseConstsConj) {k : Nat} ->
            DescPackConj consts k -> Nat
dpcProgIx consts pack = fst pack

dpcRuns :
  (consts : SurpriseConstsConj) {k : Nat} ->
  (pack : DescPackConj consts k) ->
  Deriv (Describes (ap1 (SurpriseConstsConj.enum consts)
                        (natCode (dpcProgIx consts pack)))
                    (natCode k))
dpcRuns consts pack = snd pack

------------------------------------------------------------------------
-- DescFamConj  --  family of per-day descriptions with the pigeonhole
-- bound .   Parallel to OLD  DescFam .

record DescFamConj (consts : SurpriseConstsConj) : Set where
  field
    descAt : (d : Nat) -> DescPackConj consts d
    ixBd   : (d : Nat) ->
             Lt d (suc (SurpriseConstsConj.N consts)) ->
             Lt (dpcProgIx consts (descAt d))
                (suc (SurpriseConstsConj.M consts))
    ltMN   : Lt (SurpriseConstsConj.M consts)
                (SurpriseConstsConj.N consts)

------------------------------------------------------------------------
-- Helper :  collapse the  substF  on a closed-enum  Describes  formula
-- under  ruleInst zero O .

private
  substF_collapse_conj :
    (enum : Fun1) (progIx : Nat) (k : Nat) ->
    Deriv (substF zero O (Describes (ap1 enum (natCode progIx)) (natCode k))) ->
    Deriv (eqF (ap2 runProg (ap1 enum (natCode progIx)) O) (ap1 s (natCode k)))
  substF_collapse_conj enum progIx k d =
    let progT : Term
        progT = ap1 enum (natCode progIx)

        npT : NoVar progT
        npT = NoVar_natCode progIx

        eqP : Eq (substT zero O progT) progT
        eqP = substT_NoVar zero O progT npT

        eqNc : Eq (substT zero O (natCode k)) (natCode k)
        eqNc = substT_natCode zero O k

        -- After substF, the formula is
        --   eqF (ap2 runProg (substT 0 O progT) O) (ap1 s (substT 0 O (natCode k)))
        -- (the   var 0  in the runProg-fuel slot reduces to  O  definitionally) .
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
-- The shipment .

descFamToNegs0 :
  (consts : SurpriseConstsConj) ->
  DescFamConj consts ->
  PerProgramNegConj consts (natCode zero)
descFamToNegs0 consts df k _ =
  let open SurpriseConstsConj consts using ( N ; M ; enum )

      descAt : (d : Nat) -> DescPackConj consts d
      descAt = DescFamConj.descAt df

      -- Pigeonhole input :  day  d  ->  chosen short-program index .
      ix : Nat -> Nat
      ix d = dpcProgIx consts (descAt d)

      -- Pigeonhole : Lt M N + bound -> collision among [0..N] for ix .
      coll : Collide ix N
      coll = pigeonhole ix N M (DescFamConj.ixBd df) (DescFamConj.ltMN df)

      -- Unpack the collision .
      i : Nat
      i = Collide.i_idx coll
      j : Nat
      j = Collide.j_idx coll
      i_neq_j : Not (Eq i j)
      i_neq_j = Collide.i_neq coll

      packI : DescPackConj consts i
      packI = descAt i

      packJ : DescPackConj consts j
      packJ = descAt j

      ixI : Nat
      ixI = dpcProgIx consts packI

      ixJ : Nat
      ixJ = dpcProgIx consts packJ

      progI : Term
      progI = ap1 enum (natCode ixI)

      progJ : Term
      progJ = ap1 enum (natCode ixJ)

      -- Collision : Eq (ix i) (ix j)  =  Eq ixI ixJ  (definitionally) .
      ixEq : Eq ixI ixJ
      ixEq = Collide.ix_eq coll

      -- Meta term-equality  progJ = progI  via  eqCong .
      sameProg : Eq progJ progI
      sameProg = eqSym (eqCong (\ n -> ap1 enum (natCode n)) ixEq)

      -- The open-fuel  Describes  derivations from each pack .
      runs_i : Deriv (Describes progI (natCode i))
      runs_i = dpcRuns consts packI

      runs_j : Deriv (Describes progJ (natCode j))
      runs_j = dpcRuns consts packJ

      -- Instantiate var 0 := O in each, collapsing substF .
      runs_i_O : Deriv (eqF (ap2 runProg progI O) (ap1 s (natCode i)))
      runs_i_O = substF_collapse_conj enum ixI i (ruleInst zero O runs_i)

      runs_j_O : Deriv (eqF (ap2 runProg progJ O) (ap1 s (natCode j)))
      runs_j_O = substF_collapse_conj enum ixJ j (ruleInst zero O runs_j)

      -- Rewrite  progJ -> progI  via  sameProg .
      runs_j_O_at_I :
        Deriv (eqF (ap2 runProg progI O) (ap1 s (natCode j)))
      runs_j_O_at_I =
        eqSubst (\ p -> Deriv (eqF (ap2 runProg p O) (ap1 s (natCode j))))
                 sameProg runs_j_O

      -- Determinism :  s (natCode i) = s (natCode j) .
      s_eq : Deriv (eqF (ap1 s (natCode i)) (ap1 s (natCode j)))
      s_eq = runProg_det progI O (natCode i) (natCode j)
               runs_i_O runs_j_O_at_I

      -- Strip the  s .
      eq_nc : Deriv (eqF (natCode i) (natCode j))
      eq_nc = s_inj (natCode i) (natCode j) s_eq

      -- numNeq  from  i /= j .
      neg_eq : Deriv (neg (eqF (natCode i) (natCode j)))
      neg_eq = numNeq i j i_neq_j

      -- Ex-falso DIRECTLY to the per-prog neg target ( no ConOpenInt detour ) .
      P : Formula
      P = eqF (natCode i) (natCode j)

      target : Formula
      target = neg (definable (ap1 enum (natCode k)) (natCode zero) (var (suc zero)))
  in mp (mp (axExFalso P target) eq_nc) neg_eq
