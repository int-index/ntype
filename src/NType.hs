{-# LANGUAGE TypeInType, TypeFamilies, TypeOperators, GADTs, RankNTypes,
             LambdaCase, ConstraintKinds, AllowAmbiguousTypes,
             ScopedTypeVariables, TypeApplications, MultiParamTypeClasses,
             FlexibleInstances, FlexibleContexts, UndecidableInstances #-}

module NType
  (
    -- * General definitions
    AllConstrained
  , IdentityElement
  , MonoidOf(..)
  , N(Base, Step)
  , nmap
  , nmapConstrained
  , nfold
  , nfoldConstrained

    -- * Product types
  , Rec
  , rmap
  , rmapConstrained
  , rfold
  , rfoldConstrained
  , rget
  , HList
  , Spine
  , KnownSpine(..)

    -- * Sum types
  , Union
  , umap
  , umapConstrained
  , ufold
  , ufoldConstrained
  , umatch
  , ulift
  , OpenUnion
  , ElemEv
  , Elem
  , elemEv
  ) where

import Data.Functor.Identity
import Data.Bifunctor
import Data.Kind
import Data.Void
import Data.Proxy
import Data.Type.Equality

--------------------------------------------------------------------------------
--  General definitions.
--------------------------------------------------------------------------------

type family AllConstrained c ts :: Constraint where
  AllConstrained c '[] = ()
  AllConstrained c (t : ts) = (c t, AllConstrained c ts)

type family Index x xs :: [()] where
  Index x (x : xs) = '[]
  Index x (_ : xs) = '() : Index x xs

-- The identity element for a tensor product in Hask.
type family IdentityElement (tensor :: Type -> Type -> Type)

class MonoidOf tensor m where
  mu :: tensor m m -> m
  eta :: IdentityElement tensor -> m

data N :: (Type -> Type -> Type) -> (k -> Type) -> [k] -> Type where
  Base :: !(IdentityElement tensor) -> N tensor f '[]
  Step :: !(tensor (f x) (N tensor f xs)) -> N tensor f (x:xs)

instance Eq (IdentityElement tensor) => Eq (N tensor f '[]) where
  Base u == Base v = u == v

instance Eq (tensor (f x) (N tensor f xs)) => Eq (N tensor f (x:xs)) where
  Step t1 == Step t2 = t1 == t2

instance Ord (IdentityElement tensor) => Ord (N tensor f '[]) where
  compare (Base u) (Base v) = compare u v

instance Ord (tensor (f x) (N tensor f xs)) => Ord (N tensor f (x:xs)) where
  compare (Step t1) (Step t2) = compare t1 t2

instance Show (IdentityElement tensor) => Show (N tensor f '[]) where
  showsPrec n (Base u) = showsPrec n u

instance Show (tensor (f x) (N tensor f xs)) => Show (N tensor f (x:xs)) where
  showsPrec n (Step t) = showsPrec n t

nmap ::
  forall f g xs tensor.
  Bifunctor tensor =>
  (forall a. f a -> g a) ->
  N tensor f xs ->
  N tensor g xs
nmap f = go
  where
    go :: forall xs'. N tensor f xs' -> N tensor g xs'
    go = \case
      Base b -> Base b
      Step t -> Step (bimap f go t)

nmapConstrained ::
  forall c f g xs tensor.
  (Bifunctor tensor, AllConstrained c xs) =>
  (forall a. c a => f a -> g a) ->
  N tensor f xs ->
  N tensor g xs
nmapConstrained f = go
  where
    go :: forall xs'. AllConstrained c xs' => N tensor f xs' -> N tensor g xs'
    go = \case
      Base b -> Base b
      Step t -> Step (bimap f go t)

nfold ::
  forall f xs r tensor.
  (Bifunctor tensor, MonoidOf tensor r) =>
  (forall x. f x -> r) ->
  N tensor f xs ->
  r
nfold f = go
  where
    go :: forall xs'. N tensor f xs' -> r
    go (Base b) = eta @tensor b
    go (Step t) = mu (bimap f go t)

nfoldConstrained ::
  forall c f xs r tensor.
  (Bifunctor tensor, MonoidOf tensor r, AllConstrained c xs) =>
  (forall x. c x => f x -> r) ->
  N tensor f xs ->
  r
nfoldConstrained f = go
  where
    go :: forall xs'. AllConstrained c xs' => N tensor f xs' -> r
    go (Base b) = eta @tensor b
    go (Step t) = mu (bimap f go t)

nlookup ::
  forall f g xs r t1 t2.
  Bifunctor t1 =>
  (forall x. f x -> g x -> r) ->
  (IdentityElement t1 -> IdentityElement t2 -> r) ->
  (forall a b. t1 (a -> r) (b -> r) -> t2 a b -> r) ->
  N t1 f xs ->
  N t2 g xs ->
  r
nlookup onMatch onBase onStep = go
  where
    go :: forall xs'. N t1 f xs' -> N t2 g xs' -> r
    go (Base v) (Base u) = onBase v u
    go (Step e) (Step t) = onStep (bimap onMatch go e) t

--------------------------------------------------------------------------------
--  Product types.
--------------------------------------------------------------------------------

type instance IdentityElement (,) = ()

instance Monoid m => MonoidOf (,) m where
  mu = uncurry mappend
  eta = const mempty

type Rec = N (,)

rmap ::
  forall f g xs.
  (forall a. f a -> g a) ->
  Rec f xs ->
  Rec g xs
rmap = nmap

rmapConstrained ::
  forall c f g xs.
  AllConstrained c xs =>
  (forall a. c a => f a -> g a) ->
  Rec f xs ->
  Rec g xs
rmapConstrained = nmapConstrained @c

rfold ::
  forall f xs r.
  Monoid r =>
  (forall x. f x -> r) ->
  Rec f xs ->
  r
rfold = nfold

rfoldConstrained ::
  forall c f xs r.
  (Monoid r, AllConstrained c xs) =>
  (forall x. c x => f x -> r) ->
  Rec f xs ->
  r
rfoldConstrained = nfoldConstrained @c

rget :: forall f xs a. Elem xs a => Rec f xs -> f a
rget = nlookup (\Refl -> id) absurd get (elemEv @xs @a)
  where
    get (Left f) (a, _) = f a
    get (Right f) (_, a) = f a

type HList = Rec Identity

type Spine = Rec Proxy

class KnownSpine xs where
  knownSpine :: Spine xs

instance KnownSpine '[] where
  knownSpine = Base ()

instance KnownSpine xs => KnownSpine (x:xs) where
  knownSpine = Step (Proxy, knownSpine)

--------------------------------------------------------------------------------
--  Sum types.
--------------------------------------------------------------------------------

type instance IdentityElement Either = Void

instance MonoidOf Either m where
  mu = either id id
  eta = absurd

type Union = N Either

umap ::
  forall f g xs.
  (forall a. f a -> g a) ->
  Union f xs ->
  Union g xs
umap = nmap

umapConstrained ::
  forall c f g xs.
  AllConstrained c xs =>
  (forall a. c a => f a -> g a) ->
  Union f xs ->
  Union g xs
umapConstrained = nmapConstrained @c

ufold ::
  forall f xs r.
  (forall x. f x -> r) ->
  Union f xs ->
  r
ufold = nfold

ufoldConstrained ::
  forall c f xs r.
  AllConstrained c xs =>
  (forall x. c x => f x -> r) ->
  Union f xs ->
  r
ufoldConstrained = nfoldConstrained @c

umatch :: forall f xs a. Elem xs a => Union f xs -> Maybe (f a)
umatch = nlookup (\Refl -> Just) absurd match (elemEv @xs @a)
  where
    match (Left f) (Left a) = f a
    match (Right f) (Right a) = f a
    match _ _ = Nothing

ulift :: forall f xs a. Elem xs a => f a -> Union f xs
ulift v = umap (\Refl -> v) (elemEv @xs @a)

type OpenUnion = Union Identity

type ElemEv a = Union ((:~:) a)

class Index a xs ~ n => Elem' n a xs where
  elemEv' :: ElemEv a xs

instance (xs ~ (a : xs')) => Elem' '[] a xs where
  elemEv' = Step (Left Refl)

instance
    ( Index a (x : xs') ~ ('() : n)
    , xs ~ (x : xs')
    , Elem' n a xs'
    ) => Elem' ('() : n) a xs
  where
    elemEv' = Step (Right elemEv')

class Elem' (Index x xs) x xs => Elem xs x
instance Elem' (Index x xs) x xs => Elem xs x

elemEv :: forall xs a. Elem xs a => ElemEv a xs
elemEv = elemEv'
