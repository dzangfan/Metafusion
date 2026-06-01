module Zoo where

import Control.Monad ((<=<))
import Data.Function (fix)

hylo :: (Functor f) => (f b -> b, a -> f a) -> a -> b
hylo (φ, ψ) = fix (\f -> φ . fmap f . ψ)
{-# INLINE hylo #-}

ana  :: (Functor f) => (a -> f a) -> a -> Fix f
cata :: (Functor f) => (f b -> b) -> Fix f -> b
ana  = hylo . (In, )
cata = hylo . (,out)

class Dist f m where dist :: f (m a) -> m (f a)
hyloM :: (Monad m, Functor f, Dist f m)
      => (f b -> m b, a -> m (f a))
      -> a -> m b
hyloM (φ, ψ) = fix (\f -> φ <=< (dist . fmap f) <=< ψ)
{-# INLINE hyloM #-}

newtype Fix f = In { out :: f (Fix f) }
