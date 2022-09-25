{-# LANGUAGE GADTs, IncoherentInstances, FlexibleInstances #-}

module Solve where

import Data.Typeable

main :: IO ()
main = undefined



data App a where
    L :: Show a => String -> App a
    P :: Show a => a -> App a
    A :: (Show a, Show b, Typeable a, Typeable b) => App (a -> b) -> App a -> App b

instance Typeable a => Show (App a) where
    show (L x) = x
    show (P x) = "P " ++ show x
    show (A u v) = "(" ++ show u ++ " * " ++ show v ++ ")"

instance Typeable a => Show a where
    show x = show (typeOf x)

instance (Typeable a, Typeable b) => Show (a -> b) where
    show x = "(f :: " ++ show (typeOf x) ++ ")"

term1 :: App (App String)
term1 = A (L "g") ((L "f x") :: App String)

term2 :: App (App [String])
term2 = A (L "T g") ((L "T f xs") :: App [String])

-- (P (*) * ((P (*) * P (P (:))) * (P g * f x))) * (P (T g) * T f xs)
lhs :: App (App [String])
lhs = A (A (P A) (A (A (P A) (P (P (:)))) term1)) term2


-- P (T g) * ((P (:) * (f x)) * (T f xs))
rhs :: App (App [String])
rhs = A (L "T g") (A (A (P (:)) ((L "f x") :: App (App String))) (L "T f xs"))

comp :: (Typeable a, Typeable b, Typeable c) => App ((b -> c) -> (a -> b) -> a -> c)
comp = P (.)

app :: (Typeable a, Typeable b) => a -> App ((a -> b) -> b)
app y = P ($ y)

solve :: App a -> App a
solve x = let (a, x') = solve3 x in
    if a then solve x' else x 

solve3 :: App a -> (Bool, App a)
solve3 (A u (A v w)) =
    let (_, u') = solve3 (A comp u) in
    let (_, v') = solve3 (A u' v) in
    let (_, w') = solve3 (A v' w) in
    (True, w')
solve3 (A (A u v) w) = let (a, uv') = solve3 (A u v) in
    if a then (True, A uv' w) else let (b, w') = solve3 w in
    if b then (True, A (A u v) w') else solve2 (A (A u v) w)
solve3 x = solve2 x

solve2 :: App a -> (Bool, App a)
solve2 (A (P u) (P v)) = (True, P (u v))
solve2 (A u (P y)) = (True, A (app y) u)
solve2 x = (False, x) 