# ReduceAwayVar
to avoid blowup, "Lazily" reduce away a variable.

# Installation
````
make
make install
````
# Usage.
This plugin defines the vernacular command `ReduceAwayLamVar`, which is invoked as follows:

````
Require Import ReduceAwayVar.ReduceAwayVar.
ReduceAwayLamVar defName := term.
````

`term` must be of the form `\x:A.B` (for some `x`, `A`, and `B`).
The above command will try to reduce away all the occurrences of `x` in `B`.
The result will be defined as `defName`.

For an example invokation, see
https://github.com/aa755/ReduceAwayVar/blob/coq86/theories/test.v#L24

# Authors:
Kathrin Stark and Abhishek Anand (with the help of the Coq team at the Coq implementors workshop)
