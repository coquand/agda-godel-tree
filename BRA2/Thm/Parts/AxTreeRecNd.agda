{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.Parts.AxTreeRecNd
--
-- Self-contained dispatch material for the unified-recursor node axiom
--   axTreeRecNd : Deriv (ap2 (treeRec f s) p (ap2 Pair a b)
--                       =  ap2 s (ap2 Pair p (ap2 Pair a b))
--                                (ap2 Pair (ap2 (treeRec f s) p a)
--                                          (ap2 (treeRec f s) p b))) .
--
-- Modeled after BRA2.Thm.Parts.AxRecPNd, with payT extended to depth 5 to
-- carry payF (the Fun1 leaf-handler).  The outer s-application uses payS
-- directly (no K_tr wrapping), but the inner recursive calls
-- (treeRec f s) get the full  Pair K_tr (Pair payF payS)  wrapping.

module BRA2.Thm.Parts.AxTreeRecNd where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv
open import BRA2.Thm.Tag using (tagAxTreeRecNd)
open import BRA2.Thm.TagCodes
open import BRA2.Thm.EvalHelpers

------------------------------------------------------------------------
-- Encoded proof-tree input and intended Tree output.

encAxTreeRecNd : Fun1 -> Fun2 -> Term -> Term -> Term -> Tree
encAxTreeRecNd f s p a b = nd (natCode tagAxTreeRecNd)
                              (nd (codeF1 f)
                                  (nd (codeF2 s)
                                      (nd (code p)
                                          (nd (code a) (code b)))))

outAxTreeRecNd : Fun1 -> Fun2 -> Term -> Term -> Term -> Tree
outAxTreeRecNd f s p a b =
  codeFormula (atomic (eqn (ap2 (treeRec f s) p (ap2 Pair a b))
                           (ap2 s (ap2 Pair p (ap2 Pair a b))
                                  (ap2 Pair (ap2 (treeRec f s) p a)
                                            (ap2 (treeRec f s) p b)))))

------------------------------------------------------------------------
-- body_axTreeRecNd : Fun2 dispatcher.
--
-- payT depth 5: Pair payF (Pair payS (Pair payP (Pair payA payB))).
--
-- LHS encoded : Pair K_a2 (Pair (Pair K_tr (Pair payF payS))
--                                (Pair payP (Pair K_a2 (Pair K_pair (Pair payA payB)))))
--
-- RHS encoded : Pair K_a2 (Pair payS (Pair innerArg1 innerArg2))
--   where  innerArg1 = encoded (Pair p (Pair a b))
--                    = Pair K_a2 (Pair K_pair (Pair payP (Pair K_a2 (Pair K_pair (Pair payA payB)))))
--          innerArg2 = encoded (Pair (treeRec f s p a) (treeRec f s p b))
--                    = Pair K_a2 (Pair K_pair (Pair recA recB))
--          recA      = Pair K_a2 (Pair (Pair K_tr (Pair payF payS)) (Pair payP payA))
--          recB      = Pair K_a2 (Pair (Pair K_tr (Pair payF payS)) (Pair payP payB))

body_axTreeRecNd : Fun2
body_axTreeRecNd =
  Fan
    -- LHS-build
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Fan (Lift (KT tagCode_treeRecFunc))
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd)))
                        Pair)
                   Pair)
              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Fan (Lift (KT (reify tagAp2)))
                        (Fan (Lift (KT (reify (codeF2 Pair))))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                  Pair)
                             Pair)
                        Pair)
                   Pair)
              Pair)
         Pair)
    -- RHS-build
    (Fan (Lift (KT (reify tagAp2)))
         (Fan (Lift (Comp Fst (Comp Snd Snd)))
              (Fan
                  -- innerArg1 build: Pair K_a2 (Pair K_pair (Pair payP (Pair K_a2 (Pair K_pair (Pair payA payB)))))
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 Pair))))
                            (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                 (Fan (Lift (KT (reify tagAp2)))
                                      (Fan (Lift (KT (reify (codeF2 Pair))))
                                           (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                                (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                                Pair)
                                           Pair)
                                      Pair)
                                 Pair)
                            Pair)
                       Pair)
                  -- innerArg2 build: Pair K_a2 (Pair K_pair (Pair recA recB))
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 Pair))))
                            (Fan
                                -- recA build: Pair K_a2 (Pair (Pair K_tr (Pair payF payS)) (Pair payP payA))
                                (Fan (Lift (KT (reify tagAp2)))
                                     (Fan (Fan (Lift (KT tagCode_treeRecFunc))
                                               (Fan (Lift (Comp Fst Snd))
                                                    (Lift (Comp Fst (Comp Snd Snd)))
                                                    Pair)
                                               Pair)
                                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                               (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                               Pair)
                                          Pair)
                                     Pair)
                                -- recB build: Pair K_a2 (Pair (Pair K_tr (Pair payF payS)) (Pair payP payB))
                                (Fan (Lift (KT (reify tagAp2)))
                                     (Fan (Fan (Lift (KT tagCode_treeRecFunc))
                                               (Fan (Lift (Comp Fst Snd))
                                                    (Lift (Comp Fst (Comp Snd Snd)))
                                                    Pair)
                                               Pair)
                                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                               Pair)
                                          Pair)
                                     Pair)
                                Pair)
                            Pair)
                       Pair)
                  Pair)
              Pair)
         Pair)
    Pair

------------------------------------------------------------------------
-- body_axTreeRecNd_eval (proof in abstract block to keep heavy
-- normalisation localised).

abstract

  body_axTreeRecNd_eval : (f : Fun1) (s : Fun2) (p a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeRecNd
            (ap2 Pair tagCode_axTreeRecNd
              (reify (nd (codeF1 f) (nd (codeF2 s) (nd (code p) (nd (code a') (code b'))))))) bb)
      (reify (outAxTreeRecNd f s p a' b'))))
  body_axTreeRecNd_eval f s p a' b' bb =
    let payFT  = reify (codeF1 f)
        payST  = reify (codeF2 s)
        payPT  = reify (code p)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payFT (ap2 Pair payST (ap2 Pair payPT (ap2 Pair payAT payBT)))
        a      = ap2 Pair tagCode_axTreeRecNd payT
        K_a2V  = tagAp2
        K_a2V_isValue = tagAp2_isValue
        K_a2   = reify K_a2V
        K_pairV = codeF2 Pair
        K_pairV_isValue = codeF2_isValue Pair
        K_pair = reify K_pairV
        K_trV  = leftT (codeF2 (treeRec I IfLf))
        K_trV_isValue = leftT_isValue _ (codeF2_isValue (treeRec I IfLf))
        K_tr   = reify K_trV
        ext_f  = liftCompFstSnd_evalPair tagCode_axTreeRecNd payFT
                   (ap2 Pair payST (ap2 Pair payPT (ap2 Pair payAT payBT))) bb
        ext_s  = liftFstSndSnd_evalPair3 tagCode_axTreeRecNd payFT payST
                   (ap2 Pair payPT (ap2 Pair payAT payBT)) bb
        ext_p  = liftFstSndSndSnd_evalPair4 tagCode_axTreeRecNd payFT payST payPT
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSndSndSnd_evalPair5 tagCode_axTreeRecNd payFT payST payPT payAT payBT bb
        ext_b  = liftSndSndSndSndSnd_evalPair5 tagCode_axTreeRecNd payFT payST payPT payAT payBT bb
        kTr    = liftKT_eval K_trV K_trV_isValue a bb
        ----------------------------------------------------------------
        -- Shared piece: tr_block = Pair K_tr (Pair payFT payST)
        --   (encoded treeRec f s)
        fs_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Fst (Comp Snd Snd))) a bb
                    payFT payST ext_f ext_s
        tr_block = pairOfConst_eval K_trV K_trV_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair payFT payST) fs_pair
        -- Fully encoded value:  Pair K_tr (Pair payFT payST)
        tr_blockT = ap2 Pair K_tr (ap2 Pair payFT payST)
        -- The Fun2 dispatcher producing tr_block (used in builder shapes).
        tr_blockX : Fun2
        tr_blockX = Fan (Lift (KT K_tr))
                       (Fan (Lift (Comp Fst Snd))
                            (Lift (Comp Fst (Comp Snd Snd))) Pair)
                       Pair
        ----------------------------------------------------------------
        -- Shared piece: ab_pair = Pair payAT payBT
        ab_pair  = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) a bb
                     payAT payBT ext_a ext_b
        -- Pair K_pair (Pair payAT payBT)
        kPair_ab = pairOfConst_eval K_pairV K_pairV_isValue
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                     a bb (ap2 Pair payAT payBT) ab_pair
        -- Pair K_a2 (Pair K_pair (Pair payAT payBT))
        kA2_kPair_ab = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payAT payBT)) kPair_ab
        ----------------------------------------------------------------
        -- LHS: Pair K_a2 (Pair tr_blockT (Pair payPT (Pair K_a2 (Pair K_pair (Pair payAT payBT)))))
        lhs_pT_aPair = pairOfFan_eval
                         (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                        (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                        Pair)
                                   Pair) Pair)
                         a bb
                         payPT (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                         ext_p kA2_kPair_ab
        lhs_inner = pairOfFan_eval
                      tr_blockX
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair))
                                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                          Pair)
                                     Pair) Pair)
                           Pair)
                      a bb
                      tr_blockT
                      (ap2 Pair payPT
                        (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                      tr_block lhs_pT_aPair
        lhsBuild = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan tr_blockX
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair tr_blockT
                       (ap2 Pair payPT
                         (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                     lhs_inner
        ----------------------------------------------------------------
        -- innerArg1: Pair K_a2 (Pair K_pair (Pair payPT (Pair K_a2 (Pair K_pair (Pair payAT payBT)))))
        sub1_pPair = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       (Fan (Lift (KT K_a2))
                            (Fan (Lift (KT K_pair))
                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                      Pair)
                                 Pair) Pair)
                       a bb
                       payPT (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                       ext_p kA2_kPair_ab
        sub1_kPair = pairOfConst_eval K_pairV K_pairV_isValue
                       (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                            (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                           Pair)
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair payPT
                         (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                       sub1_pPair
        sub1 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_pair))
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair))
                                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                          Pair)
                                     Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_pair
                   (ap2 Pair payPT
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                 sub1_kPair
        ----------------------------------------------------------------
        -- recA = Pair K_a2 (Pair tr_blockT (Pair payPT payAT))
        recA_pT_aT = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                       a bb payPT payAT ext_p ext_a
        recA_inner = pairOfFan_eval
                       tr_blockX
                       (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                            (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                       a bb
                       tr_blockT
                       (ap2 Pair payPT payAT)
                       tr_block recA_pT_aT
        recA = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan tr_blockX
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                           (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                      Pair)
                 a bb
                 (ap2 Pair tr_blockT (ap2 Pair payPT payAT))
                 recA_inner
        recAT = ap2 Pair K_a2 (ap2 Pair tr_blockT (ap2 Pair payPT payAT))
        -- recB = Pair K_a2 (Pair tr_blockT (Pair payPT payBT))
        recB_pT_bT = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                       a bb payPT payBT ext_p ext_b
        recB_inner = pairOfFan_eval
                       tr_blockX
                       (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                            (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                       a bb
                       tr_blockT
                       (ap2 Pair payPT payBT)
                       tr_block recB_pT_bT
        recB = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan tr_blockX
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                      Pair)
                 a bb
                 (ap2 Pair tr_blockT (ap2 Pair payPT payBT))
                 recB_inner
        recBT = ap2 Pair K_a2 (ap2 Pair tr_blockT (ap2 Pair payPT payBT))
        ----------------------------------------------------------------
        -- innerArg2: Pair K_a2 (Pair K_pair (Pair recAT recBT))
        recA_X : Fun2
        recA_X = Fan (Lift (KT K_a2))
                     (Fan tr_blockX
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                          Pair) Pair
        recB_X : Fun2
        recB_X = Fan (Lift (KT K_a2))
                     (Fan tr_blockX
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                          Pair) Pair
        rec_AB = pairOfFan_eval
                   recA_X recB_X
                   a bb recAT recBT recA recB
        sub2_kPair = pairOfConst_eval K_pairV K_pairV_isValue
                       (Fan recA_X recB_X Pair)
                       a bb
                       (ap2 Pair recAT recBT)
                       rec_AB
        sub2 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_pair))
                      (Fan recA_X recB_X Pair) Pair)
                 a bb
                 (ap2 Pair K_pair (ap2 Pair recAT recBT))
                 sub2_kPair
        ----------------------------------------------------------------
        -- Combine sub1, sub2 -> Pair sub1 sub2
        sub1_X : Fun2
        sub1_X = Fan (Lift (KT K_a2))
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair) Pair
        sub2_X : Fun2
        sub2_X = Fan (Lift (KT K_a2))
                     (Fan (Lift (KT K_pair))
                          (Fan recA_X recB_X Pair) Pair) Pair
        sub1T = ap2 Pair K_a2 (ap2 Pair K_pair
                  (ap2 Pair payPT
                    (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
        sub2T = ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair recAT recBT))
        sub1_sub2 = pairOfFan_eval
                      sub1_X sub2_X a bb sub1T sub2T sub1 sub2
        ----------------------------------------------------------------
        -- RHS: Pair K_a2 (Pair payST (Pair sub1T sub2T))
        rhs_st_pair = pairOfFan_eval
                        (Lift (Comp Fst (Comp Snd Snd)))
                        (Fan sub1_X sub2_X Pair)
                        a bb
                        payST
                        (ap2 Pair sub1T sub2T)
                        ext_s sub1_sub2
        rhsBuild = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Fan sub1_X sub2_X Pair) Pair)
                     a bb
                     (ap2 Pair payST (ap2 Pair sub1T sub2T))
                     rhs_st_pair
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan tr_blockX
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair)
                                  Pair) Pair)
                        Pair) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Fan sub1_X sub2_X Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2
           (ap2 Pair tr_blockT
             (ap2 Pair payPT
               (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
         (ap2 Pair K_a2
           (ap2 Pair payST (ap2 Pair sub1T sub2T)))
         lhsBuild rhsBuild

  ------------------------------------------------------------------
  -- Theorem 12 / Parts parametric variant for axTreeRecNd.
  -- Output is the explicit Pair structure with parametric fT, sT, pT,
  -- aT, bT slots so that Theorem 12 can plug arbitrary Term
  -- substituents at the recs slot of axTreeRecNd.

  body_axTreeRecNd_eval_param : (fT sT pT aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeRecNd
        (ap2 Pair tagCode_axTreeRecNd
          (ap2 Pair fT (ap2 Pair sT (ap2 Pair pT (ap2 Pair aT bT))))) bb)
      (ap2 Pair
        -- LHS-encoded: code (ap2 (treeRec f s) p (ap2 Pair a b))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                              (ap2 Pair fT sT))
                    (ap2 Pair pT
                      (ap2 Pair (reify tagAp2)
                        (ap2 Pair (reify (codeF2 Pair))
                          (ap2 Pair aT bT))))))
        -- RHS-encoded: code (ap2 s (ap2 Pair p (ap2 Pair a b))
        --                          (ap2 Pair (ap2 (treeRec f s) p a)
        --                                    (ap2 (treeRec f s) p b)))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair sT
            (ap2 Pair
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair pT
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair aT bT))))))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                          (ap2 Pair fT sT))
                                (ap2 Pair pT aT)))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                          (ap2 Pair fT sT))
                                (ap2 Pair pT bT))))))))))))
  body_axTreeRecNd_eval_param fT sT pT aT bT bb =
    let payFT  = fT
        payST  = sT
        payPT  = pT
        payAT  = aT
        payBT  = bT
        payT   = ap2 Pair payFT (ap2 Pair payST (ap2 Pair payPT (ap2 Pair payAT payBT)))
        a      = ap2 Pair tagCode_axTreeRecNd payT
        K_a2V  = tagAp2
        K_a2V_isValue = tagAp2_isValue
        K_a2   = reify K_a2V
        K_pairV = codeF2 Pair
        K_pairV_isValue = codeF2_isValue Pair
        K_pair = reify K_pairV
        K_trV  = leftT (codeF2 (treeRec I IfLf))
        K_trV_isValue = leftT_isValue _ (codeF2_isValue (treeRec I IfLf))
        K_tr   = reify K_trV
        ext_f  = liftCompFstSnd_evalPair tagCode_axTreeRecNd payFT
                   (ap2 Pair payST (ap2 Pair payPT (ap2 Pair payAT payBT))) bb
        ext_s  = liftFstSndSnd_evalPair3 tagCode_axTreeRecNd payFT payST
                   (ap2 Pair payPT (ap2 Pair payAT payBT)) bb
        ext_p  = liftFstSndSndSnd_evalPair4 tagCode_axTreeRecNd payFT payST payPT
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSndSndSnd_evalPair5 tagCode_axTreeRecNd payFT payST payPT payAT payBT bb
        ext_b  = liftSndSndSndSndSnd_evalPair5 tagCode_axTreeRecNd payFT payST payPT payAT payBT bb
        kTr    = liftKT_eval K_trV K_trV_isValue a bb
        ----------------------------------------------------------------
        fs_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Fst (Comp Snd Snd))) a bb
                    payFT payST ext_f ext_s
        tr_block = pairOfConst_eval K_trV K_trV_isValue
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair payFT payST) fs_pair
        tr_blockT = ap2 Pair K_tr (ap2 Pair payFT payST)
        tr_blockX : Fun2
        tr_blockX = Fan (Lift (KT K_tr))
                       (Fan (Lift (Comp Fst Snd))
                            (Lift (Comp Fst (Comp Snd Snd))) Pair)
                       Pair
        ----------------------------------------------------------------
        ab_pair  = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) a bb
                     payAT payBT ext_a ext_b
        kPair_ab = pairOfConst_eval K_pairV K_pairV_isValue
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                     a bb (ap2 Pair payAT payBT) ab_pair
        kA2_kPair_ab = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payAT payBT)) kPair_ab
        ----------------------------------------------------------------
        lhs_pT_aPair = pairOfFan_eval
                         (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                        (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                        Pair)
                                   Pair) Pair)
                         a bb
                         payPT (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                         ext_p kA2_kPair_ab
        lhs_inner = pairOfFan_eval
                      tr_blockX
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair))
                                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                          Pair)
                                     Pair) Pair)
                           Pair)
                      a bb
                      tr_blockT
                      (ap2 Pair payPT
                        (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                      tr_block lhs_pT_aPair
        lhsBuild = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan tr_blockX
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair tr_blockT
                       (ap2 Pair payPT
                         (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                     lhs_inner
        ----------------------------------------------------------------
        sub1_pPair = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       (Fan (Lift (KT K_a2))
                            (Fan (Lift (KT K_pair))
                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                      Pair)
                                 Pair) Pair)
                       a bb
                       payPT (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                       ext_p kA2_kPair_ab
        sub1_kPair = pairOfConst_eval K_pairV K_pairV_isValue
                       (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                            (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                           Pair)
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair payPT
                         (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                       sub1_pPair
        sub1 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_pair))
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair))
                                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                          Pair)
                                     Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_pair
                   (ap2 Pair payPT
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                 sub1_kPair
        ----------------------------------------------------------------
        recA_pT_aT = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                       a bb payPT payAT ext_p ext_a
        recA_inner = pairOfFan_eval
                       tr_blockX
                       (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                            (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                       a bb
                       tr_blockT
                       (ap2 Pair payPT payAT)
                       tr_block recA_pT_aT
        recA = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan tr_blockX
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                           (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                      Pair)
                 a bb
                 (ap2 Pair tr_blockT (ap2 Pair payPT payAT))
                 recA_inner
        recAT = ap2 Pair K_a2 (ap2 Pair tr_blockT (ap2 Pair payPT payAT))
        recB_pT_bT = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                       a bb payPT payBT ext_p ext_b
        recB_inner = pairOfFan_eval
                       tr_blockX
                       (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                            (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                       a bb
                       tr_blockT
                       (ap2 Pair payPT payBT)
                       tr_block recB_pT_bT
        recB = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan tr_blockX
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                      Pair)
                 a bb
                 (ap2 Pair tr_blockT (ap2 Pair payPT payBT))
                 recB_inner
        recBT = ap2 Pair K_a2 (ap2 Pair tr_blockT (ap2 Pair payPT payBT))
        ----------------------------------------------------------------
        recA_X : Fun2
        recA_X = Fan (Lift (KT K_a2))
                     (Fan tr_blockX
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                          Pair) Pair
        recB_X : Fun2
        recB_X = Fan (Lift (KT K_a2))
                     (Fan tr_blockX
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) Pair)
                          Pair) Pair
        rec_AB = pairOfFan_eval
                   recA_X recB_X
                   a bb recAT recBT recA recB
        sub2_kPair = pairOfConst_eval K_pairV K_pairV_isValue
                       (Fan recA_X recB_X Pair)
                       a bb
                       (ap2 Pair recAT recBT)
                       rec_AB
        sub2 = pairOfConst_eval K_a2V K_a2V_isValue
                 (Fan (Lift (KT K_pair))
                      (Fan recA_X recB_X Pair) Pair)
                 a bb
                 (ap2 Pair K_pair (ap2 Pair recAT recBT))
                 sub2_kPair
        ----------------------------------------------------------------
        sub1_X : Fun2
        sub1_X = Fan (Lift (KT K_a2))
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair) Pair
        sub2_X : Fun2
        sub2_X = Fan (Lift (KT K_a2))
                     (Fan (Lift (KT K_pair))
                          (Fan recA_X recB_X Pair) Pair) Pair
        sub1T = ap2 Pair K_a2 (ap2 Pair K_pair
                  (ap2 Pair payPT
                    (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
        sub2T = ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair recAT recBT))
        sub1_sub2 = pairOfFan_eval
                      sub1_X sub2_X a bb sub1T sub2T sub1 sub2
        ----------------------------------------------------------------
        rhs_st_pair = pairOfFan_eval
                        (Lift (Comp Fst (Comp Snd Snd)))
                        (Fan sub1_X sub2_X Pair)
                        a bb
                        payST
                        (ap2 Pair sub1T sub2T)
                        ext_s sub1_sub2
        rhsBuild = pairOfConst_eval K_a2V K_a2V_isValue
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Fan sub1_X sub2_X Pair) Pair)
                     a bb
                     (ap2 Pair payST (ap2 Pair sub1T sub2T))
                     rhs_st_pair
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan tr_blockX
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair)
                                  Pair) Pair)
                        Pair) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Fan sub1_X sub2_X Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2
           (ap2 Pair tr_blockT
             (ap2 Pair payPT
               (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
         (ap2 Pair K_a2
           (ap2 Pair payST (ap2 Pair sub1T sub2T)))
         lhsBuild rhsBuild
