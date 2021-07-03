||| Type for modeling set theory on types.
data Set : Type where
  SET : (a : Type) -> (a -> Set) -> Set

||| Set x is an element of another set y iff there is a term of the corresponding
||| type that gets mapped to x.
isElement : Set -> Set -> Type
isElement x (SET a f) = DPair a (\t => x = f t)

||| Similarly, x is not an element of y iff we can construct Void from 
||| the assumption that it is an element.
notIsElement : Set -> Set -> Type
notIsElement x y = (isElement x y) -> Void

||| Set of all sets that do not contain themselves. We build it on type of 
||| dependent pairs of sets equipped with a proof
||| of set not being an element of itself.
RusselSet : Set
RusselSet = SET (DPair Set (\s => notIsElement s s)) fst

-- Each set that does not contain itself is an element of a Russel set
setIsInRusselSet : {x : Set} -> notIsElement x x -> isElement x RusselSet
setIsInRusselSet {x} f = ((x ** f) ** Refl)

-- Vice versa, each set in Russel set does not contain itself
setInRusselSetNotContainsItself : {x : Set} -> isElement x RusselSet -> notIsElement x x 
setInRusselSetNotContainsItself (MkDPair (MkDPair fst y) snd) z = y (rewrite sym snd in z)

-- Russel set does not contain itself
russelSetIsNotInRusselSet : notIsElement RusselSet RusselSet
russelSetIsNotInRusselSet x = (setInRusselSetNotContainsItself x) x 

-- By applying lemma setIsInRusselSet we can show that it means that the set is in Russel set
russelSetIsInRusselSet : isElement RusselSet RusselSet
russelSetIsInRusselSet = setIsInRusselSet russelSetIsNotInRusselSet

-- However, by the definition of the Russel set that means that Russel set contains
-- itself, leading to a contradiction. We can use this to construct term of Void.
falso : Void
falso = russelSetIsNotInRusselSet russelSetIsInRusselSet

