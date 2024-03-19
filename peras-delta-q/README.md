> [!NOTE]
>
> This code has been stolen from
> https://github.com/DeltaQ-SD/Artjoms in order to simplify adaptation
> and extension to better support Peras and other network protocols
> analysis. The intention is to contribute back to the initial repository
> once an acceptable state of polish has been reached.


The Language of DeltaQ Diagrams
===============================

This repo contains an implementation of the [DeltaQ](http://www.pnsol.com/public/Algebraic-Timeliness-TR.pdf) paradigm --- a compositional language to model processes and reason about their properties.

The purpose of this work is to design a representation for the algebraic diagrams
that is easy to reason about and that can be used in further tooling.
There are three parts of this work:

  1. A modified diagram language.  It used to be called *O* in the technical report,
     now it is called *A*.
  2. Semantics of *A* given by (tabulated) functions and the ability to draw them.
  3. The ability to represent *A* expressions visually.


The A language
--------------

Conceptually, DeltaQ is a language for composing distributions of (improper) random
variables.  *A* makes it possible to define several primitive distributions (CDFs)
and introduces several connectives to build new CDFs out of existing ones.
Here is an inductive definition of the language:

```agda
  data A : Set where
    -- Constant function: K a m ≈ λ x → a
    K : I → R+ → A
    -- Uniform distribution
    uniform : R+ → R+ → A
    -- Scale down
    scaledown : I → A → A
     -- Shift right by x
    shiftright : R+ → A → A
    -- Convolution (on PDFs)
    _×_ : (a b : A) → A
    -- Pointwise +, *
    _+_ _*_ : (a b : A) → A
    -- If A were a function (ℝ+ → I), then
    -- (f ∨ g) ≈ λ x → inv (inv (f x) * inv (f y))
    _∨_ : (a b : A) → A
```

`R+` is a type of non-negative reals, and `I` is a type for the unit interval.
*A* has two primitive CDFs (K and uniform) and 6 connectives.

There are several changes from the *O* language in the technical report:

  1. It is closed.  There are no variables within the language, as all
     the expressions are compatible.  Therefore, we can simply use variables
     from of the metalanguage (Agda/Hasekell/...)
  2. Instead of introducing the notion of Dirac delta function, we introduce
     explicit `shiftright` operation which is much better behaved in numerical
     computations.
  3. Instead of attaching weights to probabilistic choice, we introduce explicit
     `scaledown` operation and the choice (`_+_`) operation that behaves as a
     point-wise addition.
  4. `K` and `uniform` have explicit values of bound on the x axis (i.e. the
     maximum x after which the function is a constant, hence nothing interesting
     is happening).  As a consequence, we can statically compute the bound on x
     axis for any expression in *A*.  It turns out that we can also compute the
     value of the CDF at that axis without performing any complex numerical
     simulations.

Implementation
--------------

There are three directories in this repository:

  * `agda` contains the model of *A*, constraints on operations on `I` and `R+`,
     an implementation of examples from [Workbench](https://github.com/DeltaQ-SD/dqsd-workbench),
     and a trivial "compilation" to python.

  * `python` contains an implementation of the backend for *A* using NumPy.
     It represents objects of *A* as (discretised) functions and implements numeric
     operations that correspond to connectives of *A*.  The main advantage of this
     implementation is the ability to use FFT for computing convolutions very efficiently.
     Finally it uses [matplotlib](https://matplotlib.org/) to visualise the CDFs.

  * `haskell` contains the model of *A*, an implementation of *A* using (discretised)
     functions and some facilities to draw *A* expressions.


Pictures
--------

An image of the introductionary example from Workbench that is generated from the following
A expression:
```haskell
doIntro :: (Rops r, Iops i) => A r i
doIntro = let
  f = Uniform (Reals.fromDouble 0) (Reals.fromDouble 1)
  g = ScaleDown (UnitInterval.fromDouble 0.95) f
  fg = f `Conv` g
  in fg
```
<img src="/img/do-intro.png" width="50%" />


An output for the A-like expression:
```haskell
boxToDot $ toB $ restrictDepth 4
  (box "a" =>= (focus "Composition" (box "b" =>= box "b1" =>= box "b2")
                -|- (named "C or C1" $ box "c" \/  (box "c1"))
                -|- box "p")
           =>= (collapse $ box "d" /\ named "Box E" (box "e")))
```
<img src="/img/diagram.jpg" width="60%" />
