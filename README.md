Codename: "I didn't think showing `Traversable List` would be this hard".

This project represents an attempt at describing some of the common type classes in Haskell (e.g. `Monad`, `Traversable`, ...), in Agda, and actually proving some of their instances to be lawful.

If this tells you nothing, but you know what a Haskell is, then directing yourself toward `Effect.Extra.Functors`, and then to `Data.Extra.Function.Instances` or `Data.Extra.Compose.Instances` might tell you more.

There is an (unpolished) solver for equalities involving `Applicatives` under `Effect.Extra.Applicatives.Solver`, for whatever that's worth.
(This is because the aforementioned proof was indeed sufficiently hard to make me write the solver instead).

`Everything` contains a list of every module in the project.
