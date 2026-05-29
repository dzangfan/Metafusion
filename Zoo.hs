module Zoo where

import Data.Function (fix)

hylo :: (Functor f) => (f b -> b, a -> f a) -> a -> b
hylo (φ, ψ) = fix (\f -> φ . fmap f . ψ)

ana  :: (Functor f) => (a -> f a) -> a -> Fix f
cata :: (Functor f) => (f b -> b) -> Fix f -> b
ana  = hylo . (In, )
cata = hylo . (,out)

newtype Fix f = In { out :: f (Fix f) }
