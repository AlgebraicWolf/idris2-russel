# idris2-russel
Implementation of Russel paradox in Idris 2.

## Version info
This proof is known to successfully type-check in Idris 2 0.4.0-2865a70a6.

## Explanation
First of all, we need to create a type for modeling sets on types. We can achieve this by thinking of sets as of types equipped with a function that maps each term of the type to some other set:
```idris
data Set : Type where
  SET : (a : Type) -> (a -> Set) -> Set
```

Using Σ types, we can express the relation of set being an element of another set. Type `isElement x y` is inhabited iff `x ∈ y`. Type `isElement x y -> Void` is inhabited iff `isElement x y` is uninhabited, meaning that we can use it to express `x ∉ y`. 
```idris
isElement : Set -> Set -> Type
isElement x (SET a f) = DPair a (\t => x = f t)

notIsElement : Set -> Set -> Type
notIsElement x y = (isElement x y) -> Void 
```

Now we can move on to the construction of a Russel set and Russel paradox. A Russel set is the set of all sets that do not contain themselves. We can construct such set on dependent pair of sets and proofs that set is not an element of itself.
```idris
RusselSet : Set
RusselSet = SET (DPair Set (\s => notIsElement s s)) fst
```

We need to additional lemmas: each set that does not contain itself is in Russel set and each set in Russel set does not contain itself:
```idris
-- Each set that does not contain itself is an element of a Russel set
setIsInRusselSet : {x : Set} -> notIsElement x x -> isElement x RusselSet
setIsInRusselSet {x} f = ((x ** f) ** Refl)

-- Vice versa, each set in Russel set does not contain itself
setInRusselSetNotContainsItself : {x : Set} -> isElement x RusselSet -> notIsElement x x 
setInRusselSetNotContainsItself (MkDPair (MkDPair fst y) snd) z = y (rewrite sym snd in z)
```

Now we can show that Russel set does not contain itself:
```idris
-- Russel set does not contain itself
russelSetIsNotInRusselSet : notIsElement RusselSet RusselSet
russelSetIsNotInRusselSet x = (setInRusselSetNotContainsItself x) x 
```

However, according to one of our lemmas, that means that Russel set contains itself. 
```idris
russelSetIsInRusselSet : isElement RusselSet RusselSet
russelSetIsInRusselSet = setIsInRusselSet russelSetIsNotInRusselSet
```

Finally, since we defined not being an element of a set as a function `notIsElement x y = (isElement x y) -> Void`, that allows us to derive a term of type Void, leading to a contradiction.
```idris
falso : Void
falso = russelSetIsNotInRusselSet russelSetIsInRusselSet
```

## Acknowledgements
Dr. Liam O'Connor's article ["The Trouble with Typing Type as Type"](http://liamoc.net/posts/2015-09-10-girards-paradox.html) that demonstrates the implementation of a similar proof in Agda was of great help while working on this example.
