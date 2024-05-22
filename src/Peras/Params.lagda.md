```agda
module Peras.Params where
```
<!--
```agda
open import Agda.Builtin.Float
open import Data.Nat using (ℕ; NonZero)
```
-->
## Peras parameters
```agda
record Params : Set where
  field U : ℕ
        K : ℕ
        R : ℕ
        L : ℕ
        A : ℕ
        τ : ℕ
        B : ℕ -- FIXME: Float
        W : ℕ

        T-nonZero : NonZero U

```
#### U
The length (in slots) of a voting round

#### K
The length of a cooldown period (in voting rounds). This needs to be large enough so that order of b\*n + k blocks are produced in time T\*K, where k is the current common-prefix parameter

#### R
Chain-ignorance period

#### L
Cutoff window (in slots) which is ignored to select block to vote for in a round

#### A
Max age for including a certificate

#### τ
The Number of votes required for quorum (3/4\*n + 2\*δ for some δ > 0)

#### B
The weight boost per vote

#### W
The weight to cut off for common prefix
