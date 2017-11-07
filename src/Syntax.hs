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
type Judgment = Bind Sig Form
type Sequent = (Sig, [Judgment], Judgment)

instance Eq (Bind Nm Tm) where (==) = aeq
instance Ord (Bind Nm Tm) where compare = acompare

instance Eq (Bind (Nm,Embed Ty) Form) where (==) = aeq
instance Ord (Bind (Nm,Embed Ty) Form) where compare = acompare

instance Eq (Bind Sig Form) where (==) = aeq
instance Ord (Bind Sig Form) where compare = acompare


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


infer :: (Alternative m, Fresh m) => Sequent -> m (Tree Sequent)
infer sqnt@(sig, gs, g)
  | g `elem` gs                   = return $ Node sqnt [] -- init
  | TT <- unsafeForm g            = return $ Node sqnt [] -- TT-R
  | FF `elem` (unsafeForm <$> gs) = return $ Node sqnt [] -- FF-L
  -- Nabla-L (local)
  -- Nabla-R (local)
  | Conj _ <- unsafeForm g = -- Conj-R
    do (lsig, Conj fs) <- unbind g
       Node sqnt <$> mapM infer [(sig,gs,bind lsig f) | f<-fs]
  | Disj _ <- unsafeForm g = -- Disj-R
    do (lsig, Disj fs) <- unbind g
       asum [infer (sig,gs,bind lsig f) | f<-fs]
  -- cut, cL, wL ??
  -- Conj-L
  -- Disj-L
  -- Imply-R
  -- Imply-L
  -- Forall-R (raising)
  -- Exists-L (raising)
  -- Forall-L (solving)
  -- Exists-R (solving)
  where
    unsafeForm = snd . unsafeUnbind
