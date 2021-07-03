# idris2-russel
Implementation of Russel paradox in Idris 2 that results in contradiction. 

## Version info
This proof is known to successfully type-check in Idris 2 0.4.0-2865a70a6.

## Explanation
First of all, we need to create a type for modeling sets on types. We can achieve this by thinking of sets as of types equipped with a function that maps each term of the type to some other set:
```idris
data Set : Type where
  SET : (a : Type) -> (a -> Set) -> Set
```

Using Σ types, we can express the relation of set being an element of another set. Type `isElement x y` is inhabited iff `x ∈ y`. Type `isElement x y -> Void` is inhabited iff `isElement x y` is uninhabited, meaning, that it is a proper way of expressing relation `x ∉ y`. 
```idris
isElement : Set -> Set -> Type
isElement x (SET a f) = DPair a (\t => x = f t)

notIsElement : Set -> Set -> Type
notIsElement x y = (isElement x y) -> Void 
```

Now we can move on to the construction of a Russel set and Russel paradox.

## Acknowledgements
Dr. Liam O'Connor's article ["The Trouble with Typing Type as Type"](http://liamoc.net/posts/2015-09-10-girards-paradox.html) that demonstrates the implementation of a similar proof in Agda was of great help while working on this example.
