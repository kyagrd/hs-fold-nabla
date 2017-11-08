{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module Syntax    where

import           Control.Applicative
import           Data.Foldable
import           Data.Tree
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
type Def = (String, Bind Sig ([Tm], Form)) -- definitional clause
type Judgment = SetBind Sig Form
type Sequent = (Sig, [Judgment], Judgment)

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


unsafeForm :: Judgment -> Form
unsafeForm = snd . unsafeUnbind

nab2sig :: Fresh m => Judgment -> m Judgment
nab2sig g | Nabla _ <- unsafeForm g =
            do (lsig, Nabla b) <- unbind g
               (xt0@(_,Embed _), f) <- unbind b
               pure $ bindSig lsig f
          | otherwise = pure g

bindSig sig f = permbind (compactSig sig f) f

compactSig sig f = [xt | xt@(x,_) <- sig, x `elem` fvf]
  where fvf = fv f :: [Nm]

infer :: (Alternative m, Fresh m) => Sequent -> m (Tree Sequent)
infer sqnt@(sig, gs, g)
  -- cut, cL, wL ??
  | g `elem` gs                   = return $ Node sqnt [] -- init
  | TT <- unsafeForm g            = return $ Node sqnt [] -- TT-R
  | FF `elem` (unsafeForm <$> gs) = return $ Node sqnt [] -- FF-L
  | (not . null) [() | Nabla _ <- unsafeForm <$> g:gs] =  -- Nabla-R, Nabla-L
    do g':gs' <- mapM nab2sig (g:gs)
       Node sqnt . (:[]) <$> infer (sig, gs', g')
  | Forall _ <- unsafeForm g = -- Forall-R (raising)
    do (lsig, Forall b) <- unbind g
       (sig', f') <- raise (sig, lsig, b)
       Node sqnt . (:[]) <$> infer (sig', gs, bindSig lsig f')
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
  -- Imply-L   TODO

  | Disj _ <- unsafeForm g = -- Disj-R
    do (lsig, Disj fs) <- unbind g
       Node sqnt . (:[]) <$> asum [infer (sig,gs,bindSig lsig f) | f<-fs]

  -- Forall-L (solving)
  -- Exists-R (solving)

-- raise :: Fresh m => (Sig, Sig, Bind (Name Tm, Embed Ty) Form) -> m (Sig, Form)
raise (sig, lsig, b) =
  do (xty@(x,Embed xt), f) <- unbind b
     h <- fresh (s2n "H")
     let (vs, etys) = unzip lsig
         tys = [ty | Embed ty <- etys]
         sig' = (h, Embed $ foldr1 Arr (tys++[xt])) : sig
         f' = subst x (foldl1 App $ map V (h:vs)) f
     return (sig, f')

raiseExistsL sig (g:gs)
  | Exists _ <- unsafeForm g = do (lsig, Exists b) <- unbind g
                                  (sig1, f') <- raise (sig, lsig, b)
                                  let g' = bindSig lsig f'
                                  (sig', gs') <- raiseExistsL sig1 gs
                                  return (sig', g':gs')
  | otherwise                = do (sig', gs') <- raiseExistsL sig gs
                                  return (sig', g:gs')
raiseExistsL sig []          = return (sig, [])

conjL :: Fresh m => [Judgment] -> m [Judgment]
conjL (g:gs) | Conj _ <- unsafeForm g =
               do (lsig, Conj fs) <- unbind g
                  ([bindSig lsig f | f<-fs] ++) <$> conjL gs
             | otherwise = (g:) <$> conjL gs
conjL [] = return []

disjL :: Fresh m => [Judgment] -> m [[Judgment]]
disjL (g:gs) | Disj _ <- unsafeForm g =
               do (lsig, Disj fs) <- unbind g
                  gss <- disjL gs
                  return [g':gs' | g' <- bindSig lsig <$> fs, gs' <- gss]
             | otherwise = map (g:) <$> disjL gs
disjL [] = return [[]]
