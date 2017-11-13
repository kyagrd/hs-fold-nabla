{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Syntax    where

import           Control.Applicative
import           Data.Foldable
import           Unbound.LocallyNameless
import           Unbound.LocallyNameless.Ops
import           Unbound.LocallyNameless.Types

type Nm = Name Tm

data Tm = V Nm
        | Lam (Bind Nm Tm)
        | App Tm Tm
     deriving (Eq,Ord,Show)

data Ty = Prop
        | TC String -- for now type constructor names are just String
        | Arr Ty Ty
        deriving (Eq,Ord,Show)

data Form
  = Forall(Bind (Nm,Embed Ty) Form)
  | Exists(Bind (Nm,Embed Ty) Form)
  | Nabla (Bind (Nm,Embed Ty) Form)
  | Imply Form Form
  | Conj [Form]
  | Disj [Form]
  | TT
  | FF
  | A String [Tm]
  deriving (Eq,Ord,Show)

type Sig = [(Nm,Embed Ty)]

type Def = Bind Sig (Form, Form) -- definition clause
-- the first form must be atomic, that is,
-- a def clause should look like "Bind sig (A p [ts], bodyform)"

type Def' = Bind Sig (Jgmt, Jgmt)

type Jgmt = SetBind Sig Form
type Sequent = (Sig, [Jgmt], Jgmt)

instance Eq (Bind Nm Tm) where (==) = aeq
instance Ord (Bind Nm Tm) where compare = acompare

instance Eq (Bind (Nm,Embed Ty) Form) where (==) = aeq
instance Ord (Bind (Nm,Embed Ty) Form) where compare = acompare

instance Eq (SetBind Sig Form) where (==) = aeq
instance Ord (SetBind Sig Form) where compare = acompare


$(derive [''Tm,''Ty,''Form])

instance Alpha Ty
instance Alpha Tm
instance Alpha Form

instance Subst Tm Tm where
  isvar (V x) = Just (SubstName x)
  isvar _     = Nothing
instance Subst Tm Ty where
instance Subst Tm Form where

lam x = Lam . bind x
app = App

occurs :: Alpha t => Nm -> t -> Bool
occurs x t = x `elem` (fv t :: [Nm])

level :: [(String,Int)] -> Form -> Int
level _ TT              = 0
level _ FF              = 0
level lvp (A p _)       = k where Just k = lookup p lvp
level lvp (Imply f1 f2) = max (1 + level lvp f1) (level lvp f2)
level lvp (Conj fs)  = maximum (level lvp <$> fs)
level lvp (Disj fs)  = maximum (level lvp <$> fs)
level lvp (Forall b)    = level lvp (snd $ unsafeUnbind b)
level lvp (Exists b)    = level lvp (snd $ unsafeUnbind b)
level lvp (Nabla b)     = level lvp (snd $ unsafeUnbind b)

lv0 :: [(String,Int)] -> Form -> Bool
lv0 _ TT            = True
lv0 _ FF            = True
lv0 lvp (A p _)     = Just 0 == lookup p lvp
lv0 lvp (Imply _ _) = False
lv0 lvp (Conj fs)   = and (lv0 lvp <$> fs)
lv0 lvp (Disj fs)   = and (lv0 lvp <$> fs)
lv0 lvp (Forall b)  = lv0 lvp (snd $ unsafeUnbind b)
lv0 lvp (Exists b)  = lv0 lvp (snd $ unsafeUnbind b)
lv0 lvp (Nabla b)   = lv0 lvp (snd $ unsafeUnbind b)

lv1 :: [(String,Int)] -> Form -> Bool
lv1 _ TT             = True
lv1 _ FF             = True
lv1 lvp (A p _)      = k <= 1 where Just k = lookup p lvp
lv1 lvp (Imply f1 f2) = lv0 lvp f1 && lv1 lvp f2
lv1 lvp (Conj fs) = and (lv1 lvp <$> fs)
lv1 lvp (Disj fs) = and (lv1 lvp <$> fs)
lv1 lvp (Forall b)   = lv1 lvp (snd $ unsafeUnbind b)
lv1 lvp (Exists b)   = lv1 lvp (snd $ unsafeUnbind b)
lv1 lvp (Nabla b)    = lv1 lvp (snd $ unsafeUnbind b)


unsafeForm :: Jgmt -> Form
unsafeForm = snd . unsafeUnbind

nab2sig :: Fresh m => Jgmt -> m Jgmt
nab2sig g | Nabla _ <- unsafeForm g =
            do (lsig, Nabla b) <- unbind g
               (xt0@(_,Embed _), f) <- unbind b
               pure $ bindSig lsig f
          | otherwise = pure g

bindSig sig f = permbind (compactSig sig f) f

compactSig sig f = [xt | xt@(x,_) <- sig, x `elem` fvf]
  where fvf = fv f :: [Nm]

-- TODO integrate matching and unification from hs-nipkow-93

-- global signature
gsig :: Sig
gsig = fmap Embed <$>
        [ (s2n"tt", TC"bool")
        , (s2n"ff", TC"bool")
        , (s2n"zero", TC"nat")
        , (s2n"succ", foldr1 Arr $ TC<$>["nat","nat"])
        ]

-- definitions  (just the plus for now)
{-
defs = [ bind ((,Embed$TC"nat")<$>[j])
          (A "plus" [      tmZ, V j,      V j ], TT                      )
       , bind ((,Embed$TC"nat")<$>[i,j,k])
          (A "plus" [ tmS(V i), V j, tmS(V k) ], A "plus" [V i, V j, V k])
       ]
  where
    tmZ = V $ s2n "zero"
    tmS = App (V $ s2n "succ")
    [i,j,k] = s2n <$>["i","j","k"]
-}

-- for now assume are args of the definition head is assumed to be variables
-- as in Tiu's thesis chapter 2
defs = [ bind ((,Embed nat)<$>[i,j,k])
          (A "plus" [V i, V j, V k],
             Disj [ Conj [ V i `eq` tmZ, V j `eq` V k ]
                  , exists (i',Embed nat) $ exists (k',Embed nat) $
                    Conj [ V i `eq` tmS(V i'), V k `eq` tmS(V k')
                         , A "plus" [V i', V j, V k']]
                  ]
          )
       ]
  where
    nat = TC"nat"
    exists x = Exists . bind x
    forall x = Forall . bind x
    eq x y = A "=" [x,y]
    tmZ = V $ s2n "zero"
    tmS = App (V $ s2n "succ")
    [i,j,k] = s2n <$>["i","j","k"]
    [i',k'] = s2n <$>["i'","k'"]

plusDef = head defs



-- raiseDef :: Fresh m => Sig -> Def -> m Def'
-- raiseDef = undefined -- TODO


{-
tmOf :: (Alternative m, Fresh m) => Sig -> Ty -> m Tm
tmOf sig Prop        = error "type of Tm cannot involve Prop"
tmOf sig (Arr t1 t2) = do x <- fresh (s2n "_a")
                          tm <- tmOf ((x,Embed t1):sig) t2
                          return $ lam x tm
tmOf sig ty@(TC a)   = asum $ uncurry tmOfApp <$> tm0tyss
   where
     tmOfApp tm0 tys = foldl1 App . (tm0 :) <$> mapM (tmOf sig) tys
     tm0tyss = [ (V c, init $ unfoldArr t) | (c,Embed t)<-gsig++sig, ty==returnTy t]
-}

tmOf :: Fresh m => Sig -> Ty -> m [Tm]
tmOf sig Prop        = return []
tmOf sig (Arr t1 t2) = do x <- fresh (s2n "_a")
                          map (lam x) <$> tmOf ((x,Embed t1):sig) t2
tmOf sig ty@(TC a)   = concat <$> mapM (uncurry tmOfApp) tm0tyss
   where
     tmOfApp tm0 tys = do tss <- mapM (tmOf sig) tys
                          return $ foldl1 App . (tm0 :) <$> tss
     tm0tyss = [ (V c, init $ unfoldArr t) | (c,Embed t)<-gsig++sig, ty==returnTy t]


returnTy = last . unfoldArr

unfoldArr (Arr t1 t2) = t1 : unfoldArr t2
unfoldArr t           = [t]

data PfTree = Thunk Sequent
            | Node Sequent [PfTree]
            | Alt Sequent [PfTree]
            deriving Show

infer :: Fresh m => Sequent -> m PfTree
infer sqnt@(sig, gs, g)
  -- cut, cL, wL ??
  | g `elem` gs                   = return $ Node sqnt [] -- init
  | TT <- unsafeForm g            = return $ Node sqnt [] -- TT-R
  | FF `elem` (unsafeForm <$> gs) = return $ Node sqnt [] -- FF-L
  | FF <- unsafeForm g            = return $ Alt sqnt [] -- FF-R
  | (not . null) [() | Nabla _ <- unsafeForm <$> g:gs] =  -- Nabla-R, Nabla-L
    do g':gs' <- mapM nab2sig (g:gs)
       Node sqnt . (:[]) <$> infer (sig, gs', g')
  | Forall _ <- unsafeForm g = -- Forall-R (raising)
    do (lsig, Forall b) <- unbind g
       (sig', g') <- raise (sig, lsig, b)
       Node sqnt . (:[]) <$> infer (sig', gs, g')
  | (not . null) [() | Exists _ <- unsafeForm <$> gs] = -- Exists-L (raising)
    do (sig', gs') <- raiseExistsL sig gs
       Node sqnt . (:[]) <$> infer (sig, gs', g)
  | Imply _ _ <- unsafeForm g = -- Imply-R
    do (lsig, Imply g1 g2) <- unbind g
       Node sqnt . (:[]) <$> infer (sig, bindSig lsig g1 : gs, bindSig lsig g2)
  | (not . null) [() | Conj _ <- unsafeForm <$> gs] = -- Conj-L
    do gs' <- conjL gs
       Node sqnt . (:[]) <$> infer (sig, gs', g)

  | Conj _ <- unsafeForm g = -- Conj-R
    do (lsig, Conj fs) <- unbind g
       Node sqnt <$> mapM infer [(sig,gs,bindSig lsig f) | f<-fs]
  | (not . null) [() | Disj _ <- unsafeForm <$> gs] = -- Disj-L
    do gss <- disjL gs
       Node sqnt <$> mapM infer [(sig, gs', g) | gs' <- gss]

  | Disj _ <- unsafeForm g = -- Disj-R
    do (lsig, Disj fs) <- unbind g
       Alt sqnt <$> mapM infer [(sig, gs, bindSig lsig f) | f<-fs]

  | Exists _ <-unsafeForm g = -- Exists-R (solving)
    pure $ Thunk sqnt -- TODO
  | (not . null) [() | Forall _ <- unsafeForm <$> gs] = -- Forall-L (solving)
    pure $ Thunk sqnt -- TODO

  -- | (not . null) [() | Imply _ _ <- unsafeForm <$> gs] = -- Imply-L
  --  pure $ Thunk sqnt -- there is no occurrences of this rule for 0/1 solver
  | otherwise = pure $ Thunk sqnt


-- raise :: Fresh m => (Sig, Sig, Bind (Name Tm, Embed Ty) Form) -> m (Sig, Form)
raise (sig, lsig, b)
  | null lsig = do (xty@(_,Embed _), f) <- unbind b
                   return (xty:sig, bindSig lsig f)
  | otherwise = do (xty@(x,Embed xt), f) <- unbind b
                   h <- fresh (s2n "H")
                   let (vs, etys) = unzip lsig
                       tys = [ty | Embed ty <- etys]
                       sig' = (h, Embed $ foldr1 Arr (tys++[xt])) : sig
                       f' = subst x (foldl1 App $ map V (h:vs)) f
                   return (sig, bindSig lsig f')

raiseExistsL sig (g:gs)
  | Exists _ <- unsafeForm g = do (lsig, Exists b) <- unbind g
                                  (sig1, g') <- raise (sig, lsig, b)
                                  (sig', gs') <- raiseExistsL sig1 gs
                                  return (sig', g':gs')
  | otherwise                = do (sig', gs') <- raiseExistsL sig gs
                                  return (sig', g:gs')
raiseExistsL sig []          = return (sig, [])

conjL :: Fresh m => [Jgmt] -> m [Jgmt]
conjL (g:gs) | Conj _ <- unsafeForm g =
               do (lsig, Conj fs) <- unbind g
                  ([bindSig lsig f | f<-fs] ++) <$> conjL gs
             | otherwise = (g:) <$> conjL gs
conjL [] = return []

disjL :: Fresh m => [Jgmt] -> m [[Jgmt]]
disjL (g:gs) | Disj _ <- unsafeForm g =
               do (lsig, Disj fs) <- unbind g
                  gss <- disjL gs
                  return [g':gs' | g' <- bindSig lsig <$> fs, gs' <- gss]
             | otherwise = map (g:) <$> disjL gs
disjL [] = return [[]]
