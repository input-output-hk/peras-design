```agda
module Peras.Params where
```
<!--
```agda
open import Data.Nat using (ℕ)
```
-->
## Peras parameters
```agda
record Params : Set where
  field T : ℕ
        K : ℕ 
        Lₗ : ℕ
        Lₕ : ℕ
        L : ℕ
        τ : ℕ
        W : ℕ
        N : ℕ
```
#### T
The length (in slots) of a voting round

#### K
The length of a cooldown period (in voting rounds). This needs to be large enough so that order of b\*n + k blocks are produced in time T\*K, where k is the current common-prefix parameter

#### Lₗ, Lₕ 
Defines the vote-candidate window is a security parameter to guarantee that there exists a block in the interval [Lₗ, Lₕ]

#### L
Max age for including vote. A constant large enough to ensure honest votes get included

#### τ
The Number of votes required for quorum (3/4\*n + 2\*δ for some δ > 0)

#### b
The weight boost per vote

#### W
The weight to cut off for common prefix

#### N
The committee size. This is a security parameter to avoid adversarially dominated committees
