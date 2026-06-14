{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParsObj -- the OBJECT MULTI-STEP relation  Pars  (the reflexive-
-- transitive closure of parallel reduction), internalised as an  E -search
-- over REDUCTION-SEQUENCE CODES (chains of Par-certificates), the object
-- analog of  T4.ChurchRosserProto.Pars  /  T4.ParConfl.ParsM :
--
--     data Pars : Tm -> Tm -> Set where
--       pdone : Pars t t
--       pmore : Par t u -> Pars u v -> Pars t v
--
-- A CHAIN is a tagged-pair list of certificates (cf. T4.ParCert):
--     chNil v       = Pair (natCode 1) v                 -- pdone : carries the vertex v
--     chCons d rest = Pair (natCode 2) (Pair d rest)     -- pmore : head cert d , tail chain
-- (tags 1/2 are SUCCESSORS so both codes are fold NODES  pi (s _) _ ; the
-- empty chain CARRIES its vertex, since an empty reduction sequence does not
-- otherwise determine its endpoints).
--
-- Over chain codes we build three RECURSIVE OBJECT functions, as
-- T4.FoldRec.fold course-of-values folds (template: T4.ParEnds):
--     parsSrc (chNil v)       = v          parsSrc (chCons d rest) = src d
--     parsTgt (chNil v)       = v          parsTgt (chCons d rest) = parsTgt rest
--     isChain (chNil v)       = O          isChain (chCons d rest) =
--         pi (pi (isCert d) (isChain rest)) (eqTest (tgt d) (parsSrc rest))
-- where  src/tgt/isCert  are the single-cert endpoint maps (T4.ParEnds) and
-- eqTest a b = pi (sub a b)(sub b a) = O  iff  a = b .  So  isChain c = O  iff
-- c codes a genuine reduction sequence (each cert valid, endpoints composable).
--
-- The object predicate (cf. T4.ParIntro) and its introduction rules:
--     Pars t u  :=  E (parsBody t u)
--     parsIntro  : ParsCert (code t)(code u) -> Deriv (Pars (code t)(code u))
--     parsObjOf  : ParsM t u -> Deriv (Pars (code t)(code u))   (the bridge:
--                  EVERY meta multi-step is an object Pars-derivation)
-- where  ParsCert  is the relational record (witness chain + side conditions)
-- and  parsDone / parsMore  are its  pdone / pmore  builders.  No holes,
-- no postulates, no termination warnings.

module T4.ParsObj where

open import T4.Base

open import T4.FoldRec
open import T4.CoVSpecUniv  using ( HistP_sbt )
open import T4.Stability    using ( HPsbt )
open import T4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import T4.LeqMono      using ( leq_sigma_right ; leq_pi_right ; leq_trans )
open import T4.LenR         using ( get_rc )
open import T4.ProgParse    using ( get_tag )

open import T4.ParEnds using
  ( src ; tgt ; isCert ; lcIdx ; rcIdx ; pi_O_O )
open import T4.ParReflPres using
  ( Tm ; ze ; su ; ad ; code
  ; ParCert ; wit ; valid ; srcEq ; tgtEq )
open import T4.ParCertOf using ( certOf )
open import T4.ParTri    using ( ParM )
open import T4.ParConfl  using ( ParsM ; pdone ; pmore )
open import T4.ParIntro  using
  ( noVarCode ; eqTestF ; eqTestF_app ; eqTest_zero ; eqTestF_const_zero )
open import T4.Thm12.ConstTermFun1 using ( constTermFun1 )

open import BRA3.Church         using ( pi ; sigma ; tau ; sub )
open import BRA3.ChurchLeq      using ( leq )
open import BRA3.CourseOfValues using ( iter )
open import T4.CoVSpec          using ( cov_spec )
open import BRA3.PairAlgebra    using ( Z ; axZ ; Post ; axPost ; compose1U ; compose1U_eq )
open import BRA3.Dispatch       using ( condFork ; condFork_false ; condFork_true_nc ; constN ; constN_eq )
open import BRA3.SubT.NatEq     using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq  using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  Chain coding.

chNil : Term -> Term
chNil vt = ap2 Pair (natCode 1) vt

chCons : Term -> Term -> Term
chCons d rest = ap2 Pair (natCode 2) (ap2 Pair d rest)

------------------------------------------------------------------------
-- SECTION 1.  Shared fold skeleton (one test ; tag 1 = nil , tag 2 = cons).

test1 : Fun1
test1 = C natEqF get_tag (constN 1)

-- the step body of a 2-way fold with cells  cellNil / cellCons .
stepOf : Fun1 -> Fun1 -> Fun1
stepOf cellNil cellCons = C condFork (C pi cellNil cellCons) test1

foldOf : Fun1 -> Fun1 -> Fun1 -> Fun1
foldOf g cellNil cellCons = fold g (Post (stepOf cellNil cellCons) pi)

------------------------------------------------------------------------
-- SECTION 2.  Generic node plumbing for a 2-cell fold (parametric in the
-- base  g  and the two cells ; mirrors T4.ParEnds.NodePlumb + Dispatch,
-- specialised to the single tag test).

module NP (g cellNil cellCons : Fun1) (A b : Term) where
  stepBody : Fun1
  stepBody = stepOf cellNil cellCons

  node : Term
  node = ap2 pi (ap1 s A) b
  P_outer : Term
  P_outer = pi_succ_outer A b
  prev : Term
  prev = ap2 (cov_spec g (Post stepBody pi)) O P_outer
  input_pkg : Term
  input_pkg = ap2 pi P_outer (ap1 Snd prev)

  -- fold g (Post stepBody pi) at the node fires the step body on input_pkg.
  np_unfold : Deriv (eqF (ap1 (fold g (Post stepBody pi)) node) (ap1 stepBody input_pkg))
  np_unfold =
    ruleTrans (fold_node_unfold g (Post stepBody pi) A b)
              (axPost stepBody pi P_outer (ap1 Snd prev))

  np_head : Deriv (eqF (ap1 get_tag input_pkg) (ap1 s A))
  np_head =
    let t1 : Deriv (eqF (ap1 get_tag input_pkg) (ap1 Fst (ap1 get_newK input_pkg)))
        t1 = compose1U_eq Fst get_newK input_pkg
        t2 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
        t2 = get_newK_at_pi P_outer (ap1 Snd prev)
        t3 : Deriv (eqF (ap1 Fst (ap1 s P_outer)) (ap1 Fst node))
        t3 = cong1 Fst (ruleSym (pi_at_succ A b))
        t4 : Deriv (eqF (ap1 Fst node) (ap1 s A))
        t4 = axFst (ap1 s A) b
    in ruleTrans t1 (ruleTrans (cong1 Fst t2) (ruleTrans t3 t4))

  np_rc : Deriv (eqF (ap1 get_rc input_pkg) b)
  np_rc =
    let s1 : Deriv (eqF (ap1 get_rc input_pkg) (ap1 Snd (ap1 get_newK input_pkg)))
        s1 = compose1U_eq Snd get_newK input_pkg
        s2 : Deriv (eqF (ap1 get_newK input_pkg) (ap1 s P_outer))
        s2 = get_newK_at_pi P_outer (ap1 Snd prev)
        s3 : Deriv (eqF (ap1 Snd (ap1 s P_outer)) (ap1 Snd node))
        s3 = cong1 Snd (ruleSym (pi_at_succ A b))
        s4 : Deriv (eqF (ap1 Snd node) b)
        s4 = axSnd (ap1 s A) b
    in ruleTrans s1 (ruleTrans (cong1 Snd s2) (ruleTrans s3 s4))

  leq_b_P : Deriv (leq b P_outer)
  leq_b_P = leq_sigma_right (ap2 sigma (ap2 sigma A b) (ap1 tau (ap2 sigma A b))) b

  np_lookup_gen :
    (idx : Fun1) (ct : Term) ->
    Deriv (eqF (ap1 idx input_pkg) ct) ->
    Deriv (leq ct P_outer) ->
    Deriv (eqF (ap1 (lookupAt idx) input_pkg) (ap1 (fold g (Post stepBody pi)) ct))
  np_lookup_gen idx ct idx_eq leq_ct =
    let get_K_value : Deriv (eqF (ap1 get_K input_pkg) P_outer)
        get_K_value = get_K_at_pi P_outer (ap1 Snd prev)
        get_table_value :
          Deriv (eqF (ap1 get_table input_pkg)
                      (HistP_sbt g (Post stepBody pi) O P_outer))
        get_table_value = get_table_at_pi P_outer (ap1 Snd prev)
        u1 : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                        (ap1 Fst (ap2 (iter Snd) (ap1 get_table input_pkg)
                                  (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg)))))
        u1 = lookupAt_unfold idx input_pkg
        sub_eq : Deriv (eqF (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                            (ap2 sub P_outer ct))
        sub_eq = ruleTrans (congL sub (ap1 idx input_pkg) get_K_value)
                           (congR sub P_outer idx_eq)
        iter_eq : Deriv (eqF (ap2 (iter Snd) (ap1 get_table input_pkg)
                              (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg)))
                              (ap2 (iter Snd) (HistP_sbt g (Post stepBody pi) O P_outer)
                              (ap2 sub P_outer ct)))
        iter_eq =
          ruleTrans (congL (iter Snd)
                      (ap2 sub (ap1 get_K input_pkg) (ap1 idx input_pkg))
                      get_table_value)
                    (congR (iter Snd) (HistP_sbt g (Post stepBody pi) O P_outer) sub_eq)
        lookup_to_HP : Deriv (eqF (ap1 (lookupAt idx) input_pkg)
                                  (HPsbt g (Post stepBody pi) O ct P_outer))
        lookup_to_HP = ruleTrans u1 (cong1 Fst iter_eq)
        HP_to_fold : Deriv (eqF (HPsbt g (Post stepBody pi) O ct P_outer)
                                (ap1 (fold g (Post stepBody pi)) ct))
        HP_to_fold = lookup_eq_fold g (Post stepBody pi) ct P_outer leq_ct
    in ruleTrans lookup_to_HP HP_to_fold

  -- Dispatch: stepBody input = condFork (pi cellNil cellCons input)(test1 input).
  pairCell : Term
  pairCell = ap1 (C pi cellNil cellCons) input_pkg

  fst_pairCell : Deriv (eqF (ap1 Fst pairCell) (ap1 cellNil input_pkg))
  fst_pairCell = ruleTrans (cong1 Fst (ax_C pi cellNil cellCons input_pkg))
                           (axFst (ap1 cellNil input_pkg) (ap1 cellCons input_pkg))
  snd_pairCell : Deriv (eqF (ap1 Snd pairCell) (ap1 cellCons input_pkg))
  snd_pairCell = ruleTrans (cong1 Snd (ax_C pi cellNil cellCons input_pkg))
                           (axSnd (ap1 cellNil input_pkg) (ap1 cellCons input_pkg))

  sb_eq : Deriv (eqF (ap1 stepBody input_pkg)
                     (ap2 condFork pairCell (ap1 test1 input_pkg)))
  sb_eq = ax_C condFork (C pi cellNil cellCons) test1 input_pkg

  test1_val : Deriv (eqF (ap1 test1 input_pkg) (ap2 natEqF (ap1 s A) (natCode 1)))
  test1_val =
    ruleTrans (ax_C natEqF get_tag (constN 1) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 1) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq 1 input_pkg)))

  -- nil-branch (tag = 1) collapse:  given the test FIRES, stepBody = cellNil .
  collapse_fst : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O)) ->
                 Deriv (eqF (ap1 (fold g (Post stepBody pi)) node) (ap1 cellNil input_pkg))
  collapse_fst t1_fire =
    ruleTrans np_unfold
      (ruleTrans sb_eq
        (ruleTrans (congR condFork pairCell t1_fire)
          (ruleTrans (condFork_true_nc pairCell O) fst_pairCell)))

  -- cons-branch (tag = 2) collapse:  given the test SKIPS, stepBody = cellCons .
  collapse_snd : Deriv (eqF (ap1 test1 input_pkg) O) ->
                 Deriv (eqF (ap1 (fold g (Post stepBody pi)) node) (ap1 cellCons input_pkg))
  collapse_snd t1_O =
    ruleTrans np_unfold
      (ruleTrans sb_eq
        (ruleTrans (congR condFork pairCell t1_O)
          (ruleTrans (condFork_false pairCell) snd_pairCell)))

------------------------------------------------------------------------
-- SECTION 3.  parsSrc  (NON-recursive: nil -> the vertex, cons -> src head).

cellNilS : Fun1
cellNilS = get_rc                         -- chNil v -> v
cellConsS : Fun1
cellConsS = compose1U src lcIdx           -- chCons d rest -> src d

parsSrc : Fun1
parsSrc = foldOf Z cellNilS cellConsS

parsSrc_nil : (vt : Term) -> Deriv (eqF (ap1 parsSrc (chNil vt)) vt)
parsSrc_nil vt =
  let open NP Z cellNilS cellConsS O vt
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) np_rc   -- cellNilS input = get_rc input = b = vt

parsSrc_cons : (d rest : Term) ->
  Deriv (eqF (ap1 parsSrc (chCons d rest)) (ap1 src d))
parsSrc_cons d rest =
  let open NP Z cellNilS cellConsS (natCode 1) (ap2 Pair d rest)
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      lcIdx_eq : Deriv (eqF (ap1 lcIdx input_pkg) d)
      lcIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                           (ruleTrans (cong1 Fst np_rc) (axFst d rest))
      cellConsS_val : Deriv (eqF (ap1 cellConsS input_pkg) (ap1 src d))
      cellConsS_val = ruleTrans (compose1U_eq src lcIdx input_pkg)
                                (cong1 src lcIdx_eq)
  in ruleTrans (collapse_snd t1_O) cellConsS_val

------------------------------------------------------------------------
-- SECTION 4.  parsTgt  (cons recurses on the tail chain).

cellNilT : Fun1
cellNilT = get_rc                         -- chNil v -> v
cellConsT : Fun1
cellConsT = lookupAt rcIdx                -- chCons d rest -> parsTgt rest

parsTgt : Fun1
parsTgt = foldOf Z cellNilT cellConsT

parsTgt_nil : (vt : Term) -> Deriv (eqF (ap1 parsTgt (chNil vt)) vt)
parsTgt_nil vt =
  let open NP Z cellNilT cellConsT O vt
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) np_rc

parsTgt_cons : (d rest : Term) ->
  Deriv (eqF (ap1 parsTgt (chCons d rest)) (ap1 parsTgt rest))
parsTgt_cons d rest =
  let open NP Z cellNilT cellConsT (natCode 1) (ap2 Pair d rest)
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      rcIdx_eq : Deriv (eqF (ap1 rcIdx input_pkg) rest)
      rcIdx_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                           (ruleTrans (cong1 Snd np_rc) (axSnd d rest))
      leq_rest : Deriv (leq rest P_outer)
      leq_rest = leq_trans rest (ap2 pi d rest) P_outer (leq_pi_right d rest) leq_b_P
      rec : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 parsTgt rest))
      rec = np_lookup_gen rcIdx rest rcIdx_eq leq_rest
  in ruleTrans (collapse_snd t1_O) rec

------------------------------------------------------------------------
-- SECTION 5.  isChain  (cons recurses + checks composability of d , rest).
--   isChain (chCons d rest) =
--     pi (pi (isCert d)(isChain rest)) (pi (sub (tgt d)(parsSrc rest))
--                                          (sub (parsSrc rest)(tgt d)))

isCertD : Fun1                            -- isCert (Fst payload)
isCertD = compose1U isCert lcIdx
tgtD : Fun1                               -- tgt (Fst payload)
tgtD = compose1U tgt lcIdx
psrcRest : Fun1                           -- parsSrc (Snd payload)
psrcRest = compose1U parsSrc rcIdx

cellNilC : Fun1
cellNilC = Z                              -- chNil v -> O (valid)
cellConsC : Fun1
cellConsC = C pi (C pi isCertD (lookupAt rcIdx)) (eqTestF tgtD psrcRest)

isChain : Fun1
isChain = foldOf Z cellNilC cellConsC

isChain_nil : (vt : Term) -> Deriv (eqF (ap1 isChain (chNil vt)) O)
isChain_nil vt =
  let open NP Z cellNilC cellConsC O vt
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (axZ input_pkg)   -- cellNilC input = Z input = O

isChain_cons : (d rest : Term) ->
  Deriv (eqF (ap1 isChain (chCons d rest))
             (ap2 pi (ap2 pi (ap1 isCert d) (ap1 isChain rest))
                     (ap2 pi (ap2 sub (ap1 tgt d) (ap1 parsSrc rest))
                             (ap2 sub (ap1 parsSrc rest) (ap1 tgt d)))))
isChain_cons d rest =
  let open NP Z cellNilC cellConsC (natCode 1) (ap2 Pair d rest)
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)
      lcIdx_eq : Deriv (eqF (ap1 lcIdx input_pkg) d)
      lcIdx_eq = ruleTrans (compose1U_eq Fst get_rc input_pkg)
                           (ruleTrans (cong1 Fst np_rc) (axFst d rest))
      rcIdx_eq : Deriv (eqF (ap1 rcIdx input_pkg) rest)
      rcIdx_eq = ruleTrans (compose1U_eq Snd get_rc input_pkg)
                           (ruleTrans (cong1 Snd np_rc) (axSnd d rest))
      leq_rest : Deriv (leq rest P_outer)
      leq_rest = leq_trans rest (ap2 pi d rest) P_outer (leq_pi_right d rest) leq_b_P
      -- the four sub-values
      isCertD_val : Deriv (eqF (ap1 isCertD input_pkg) (ap1 isCert d))
      isCertD_val = ruleTrans (compose1U_eq isCert lcIdx input_pkg)
                              (cong1 isCert lcIdx_eq)
      ischRest_val : Deriv (eqF (ap1 (lookupAt rcIdx) input_pkg) (ap1 isChain rest))
      ischRest_val = np_lookup_gen rcIdx rest rcIdx_eq leq_rest
      tgtD_val : Deriv (eqF (ap1 tgtD input_pkg) (ap1 tgt d))
      tgtD_val = ruleTrans (compose1U_eq tgt lcIdx input_pkg)
                           (cong1 tgt lcIdx_eq)
      psrcRest_val : Deriv (eqF (ap1 psrcRest input_pkg) (ap1 parsSrc rest))
      psrcRest_val = ruleTrans (compose1U_eq parsSrc rcIdx input_pkg)
                               (cong1 parsSrc rcIdx_eq)
      -- left conjunct:  pi (isCert d)(isChain rest)
      inner_val : Deriv (eqF (ap1 (C pi isCertD (lookupAt rcIdx)) input_pkg)
                             (ap2 pi (ap1 isCert d) (ap1 isChain rest)))
      inner_val =
        ruleTrans (ax_C pi isCertD (lookupAt rcIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rcIdx) input_pkg) isCertD_val)
                     (congR pi (ap1 isCert d) ischRest_val))
      -- right conjunct:  eqTest (tgt d)(parsSrc rest)
      subA : Deriv (eqF (ap2 sub (ap1 tgtD input_pkg) (ap1 psrcRest input_pkg))
                        (ap2 sub (ap1 tgt d) (ap1 parsSrc rest)))
      subA = ruleTrans (congL sub (ap1 psrcRest input_pkg) tgtD_val)
                       (congR sub (ap1 tgt d) psrcRest_val)
      subB : Deriv (eqF (ap2 sub (ap1 psrcRest input_pkg) (ap1 tgtD input_pkg))
                        (ap2 sub (ap1 parsSrc rest) (ap1 tgt d)))
      subB = ruleTrans (congL sub (ap1 tgtD input_pkg) psrcRest_val)
                       (congR sub (ap1 parsSrc rest) tgtD_val)
      eqtest_val : Deriv (eqF (ap1 (eqTestF tgtD psrcRest) input_pkg)
                              (ap2 pi (ap2 sub (ap1 tgt d) (ap1 parsSrc rest))
                                      (ap2 sub (ap1 parsSrc rest) (ap1 tgt d))))
      eqtest_val =
        ruleTrans (eqTestF_app tgtD psrcRest input_pkg)
          (ruleTrans (congL pi (ap2 sub (ap1 psrcRest input_pkg) (ap1 tgtD input_pkg)) subA)
                     (congR pi (ap2 sub (ap1 tgt d) (ap1 parsSrc rest)) subB))
      cellConsC_val :
        Deriv (eqF (ap1 cellConsC input_pkg)
                   (ap2 pi (ap2 pi (ap1 isCert d) (ap1 isChain rest))
                           (ap2 pi (ap2 sub (ap1 tgt d) (ap1 parsSrc rest))
                                   (ap2 sub (ap1 parsSrc rest) (ap1 tgt d)))))
      cellConsC_val =
        ruleTrans (ax_C pi (C pi isCertD (lookupAt rcIdx)) (eqTestF tgtD psrcRest) input_pkg)
          (ruleTrans (congL pi (ap1 (eqTestF tgtD psrcRest) input_pkg) inner_val)
                     (congR pi (ap2 pi (ap1 isCert d) (ap1 isChain rest)) eqtest_val))
  in ruleTrans (collapse_snd t1_O) cellConsC_val

------------------------------------------------------------------------
-- SECTION 6.  The relational certificate  ParsCert  and its builders.

record ParsCert (t u : Term) : Set where
  constructor mkParsCert
  field
    pwit   : Term
    pvalid : Deriv (eqF (ap1 isChain pwit) O)
    psrcEq : Deriv (eqF (ap1 parsSrc pwit) t)
    ptgtEq : Deriv (eqF (ap1 parsTgt pwit) u)
open ParsCert public

-- pdone :  the empty chain at vertex  code t  certifies  Pars (code t)(code t) .
parsDone : (t : Tm) -> ParsCert (code t) (code t)
parsDone t =
  mkParsCert (chNil (code t))
             (isChain_nil (code t)) (parsSrc_nil (code t)) (parsTgt_nil (code t))

-- pmore :  prepend a single Par-cert  (ParCert t u)  to a chain  (ParsCert u w) .
parsMore : (t uu w : Term) ->
  ParCert t uu -> ParsCert uu w -> ParsCert t w
parsMore t uu w pc psc =
  mkParsCert (chCons (wit pc) (pwit psc)) chainValid srcOK tgtOK
  where
    d : Term
    d = wit pc
    r : Term
    r = pwit psc
    -- isChain (chCons d r) = pi (pi (isCert d)(isChain r)) (eqTest (tgt d)(parsSrc r)) = O
    innerZero : Deriv (eqF (ap2 pi (ap1 isCert d) (ap1 isChain r)) O)
    innerZero =
      ruleTrans (congL pi (ap1 isChain r) (valid pc))
        (ruleTrans (congR pi O (pvalid psc)) pi_O_O)
    -- tgt d = u  and  parsSrc r = u , so they are equal, so eqTest = O.
    tgt_eq_psrc : Deriv (eqF (ap1 tgt d) (ap1 parsSrc r))
    tgt_eq_psrc = ruleTrans (tgtEq pc) (ruleSym (psrcEq psc))
    eqtestZero :
      Deriv (eqF (ap2 pi (ap2 sub (ap1 tgt d) (ap1 parsSrc r))
                         (ap2 sub (ap1 parsSrc r) (ap1 tgt d))) O)
    eqtestZero = eqTest_zero (ap1 tgt d) (ap1 parsSrc r) tgt_eq_psrc
    chainValid : Deriv (eqF (ap1 isChain (chCons d r)) O)
    chainValid =
      ruleTrans (isChain_cons d r)
        (ruleTrans (congL pi (ap2 pi (ap2 sub (ap1 tgt d) (ap1 parsSrc r))
                                     (ap2 sub (ap1 parsSrc r) (ap1 tgt d)))
                            innerZero)
          (ruleTrans (congR pi O eqtestZero) pi_O_O))
    srcOK : Deriv (eqF (ap1 parsSrc (chCons d r)) t)
    srcOK = ruleTrans (parsSrc_cons d r) (srcEq pc)
    tgtOK : Deriv (eqF (ap1 parsTgt (chCons d r)) w)
    tgtOK = ruleTrans (parsTgt_cons d r) (ptgtEq psc)

------------------------------------------------------------------------
-- SECTION 7.  The object  Pars  predicate and its introduction rules.
--   Pars t u  :=  E (parsBody t u)  -- exists a valid chain from t to u.

parsBody : Term -> Term -> Fun1
parsBody t uu =
  C pi (C pi isChain (eqTestF parsSrc (constTermFun1 t)))
       (eqTestF parsTgt (constTermFun1 uu))

parsBody_app : (t uu d : Term) ->
  Deriv (eqF (ap1 (parsBody t uu) d)
             (ap2 pi (ap2 pi (ap1 isChain d)
                             (ap1 (eqTestF parsSrc (constTermFun1 t)) d))
                     (ap1 (eqTestF parsTgt (constTermFun1 uu)) d)))
parsBody_app t uu d =
  ruleTrans (ax_C pi (C pi isChain (eqTestF parsSrc (constTermFun1 t)))
                     (eqTestF parsTgt (constTermFun1 uu)) d)
    (congL pi (ap1 (eqTestF parsTgt (constTermFun1 uu)) d)
       (ax_C pi isChain (eqTestF parsSrc (constTermFun1 t)) d))

Pars : Term -> Term -> Formula
Pars t uu = E (parsBody t uu)

parsIntro : (t uu : Tm) -> ParsCert (code t) (code uu) ->
            Deriv (Pars (code t) (code uu))
parsIntro t uu psc =
  E_intro (parsBody (code t) (code uu)) (pwit psc) bodyZero
  where
    w : Term
    w = pwit psc
    eSrc : Deriv (eqF (ap1 (eqTestF parsSrc (constTermFun1 (code t))) w) O)
    eSrc = eqTestF_const_zero parsSrc (code t) (noVarCode t) w (psrcEq psc)
    eTgt : Deriv (eqF (ap1 (eqTestF parsTgt (constTermFun1 (code uu))) w) O)
    eTgt = eqTestF_const_zero parsTgt (code uu) (noVarCode uu) w (ptgtEq psc)
    innerZero :
      Deriv (eqF (ap2 pi (ap1 isChain w)
                         (ap1 (eqTestF parsSrc (constTermFun1 (code t))) w)) O)
    innerZero =
      ruleTrans (congL pi (ap1 (eqTestF parsSrc (constTermFun1 (code t))) w) (pvalid psc))
        (ruleTrans (congR pi O eSrc) pi_O_O)
    outerZero :
      Deriv (eqF (ap2 pi (ap2 pi (ap1 isChain w)
                                 (ap1 (eqTestF parsSrc (constTermFun1 (code t))) w))
                         (ap1 (eqTestF parsTgt (constTermFun1 (code uu))) w)) O)
    outerZero =
      ruleTrans (congL pi (ap1 (eqTestF parsTgt (constTermFun1 (code uu))) w) innerZero)
        (ruleTrans (congR pi O eTgt) pi_O_O)
    bodyZero : Deriv (eqF (ap1 (parsBody (code t) (code uu)) w) O)
    bodyZero = ruleTrans (parsBody_app (code t) (code uu) w) outerZero

------------------------------------------------------------------------
-- SECTION 8.  The bridge: meta multi-step -> object  Pars  derivation.
--   parsCertOf : ParsM t u -> ParsCert (code t)(code u)   (meta induction)
--   parsObjOf  : ParsM t u -> Deriv (Pars (code t)(code u))

parsCertOf : {t u : Tm} -> ParsM t u -> ParsCert (code t) (code u)
parsCertOf (pdone {t})          = parsDone t
parsCertOf (pmore {t} {uu} {vv} p ps) =
  parsMore (code t) (code uu) (code vv) (certOf p) (parsCertOf ps)

parsObjOf : (t uu : Tm) -> ParsM t uu -> Deriv (Pars (code t) (code uu))
parsObjOf t uu psm = parsIntro t uu (parsCertOf psm)

parsObjDone : (t : Tm) -> Deriv (Pars (code t) (code t))
parsObjDone t = parsIntro t t (parsDone t)
