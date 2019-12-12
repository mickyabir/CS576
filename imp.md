The IMP-SEMANTICS
=================

These are the semantics of IMP in Maude, including a built-in List
datastructure.

```maude

set include BOOL off .

fmod FVP-NAT is
  sort Bool .
  op true  : -> Bool [ctor metadata "0"] .
  op false : -> Bool [ctor metadata "1"] .

  sort Nat NzNat .
  subsort NzNat < Nat .
  op 0 : -> Nat   [ctor metadata "2"] .
  op 1 : -> NzNat [ctor metadata "3"] .
  op _+_ : Nat Nat   ->   Nat [ctor assoc comm id: 0 metadata "4"] .
  op _+_ : NzNat Nat -> NzNat [ctor ditto            metadata "4"] .

  var N M : Nat .
  var Z   : NzNat .

  op _monus_ : Nat Nat -> Nat [metadata "5"] .
  eq  N      monus (N + M) = 0 [variant] .
  eq (N + Z) monus  N      = Z [variant] .

  op _<=_ : Nat Nat -> Bool [metadata "6"] .
  eq N     <= N + M = true  [variant] .
  eq N + Z <= N     = false [variant] .

  op _<_ : Nat Nat -> Bool [metadata "7"] .
  eq N     < N + Z = true  [variant] .
  eq N + M < N     = false [variant] .

  op sd : Nat Nat -> Nat [comm metadata "8"] .
  eq sd(N + Z, N    ) = Z [variant] .
  eq sd(N    , N + M) = M [variant] .
endfm

fmod FVP-NAT-MULT is
  pr FVP-NAT .

  var N : Nat . var NzN NzN' : NzNat .

  op _*_ : Nat Nat -> Nat [assoc comm metadata "9"] .
  ---------------------------------------------------
  eq N * 0 =  0 [variant] .
  eq N * 1 =  N [variant] .

  eq N * (NzN + NzN') = (N * NzN) + (N * NzN') .
endfm

```

The theory of Lists
-------------------

Here we present the theory of Lists that is incorporated into the IMP language.
The operations that we use in the language are built on top of list
concatenation constructor, denoted by `$`, the standard head and tail operations, and
the `isEmpty` function, which we use to define the semantics of `empty`.

```maude

fmod IMP-LIST is
  pr FVP-NAT .
  sort List .
  subsort Nat < List .

  op nil      :           -> List    [ctor metadata "10"] .
  op _$_      : List List -> List    [ctor id: nil assoc metadata "11"] .

  vars N X Y : Nat .
  var L L' : List .

  op head : List -> Nat                [metadata "13"] .

```

The definition of head is purposefully partial. We define a partial
function on Lists since `head(nil)` was chosen to be undefined in our
language, and therefore `head` returns a `Nat`. The `tail` and `isEmpty`
functions are defined as expected.

```maude

  eq head(N $ L) = N                   [variant] .

  op tail : List -> List                [metadata "14"] .

  eq tail(nil) = nil [variant] .
  eq tail(N $ L) = L [variant] .

  op isEmpty  : List -> Bool    [metadata "15"] .

  eq isEmpty(nil) = true    [variant] .
  eq isEmpty(N $ L) = false [variant] .

  eq head(L) $ tail(L) = L .
endfm

```

This module defines the variables of IMP, which are constructors of sort `Id` in
our theory. We also have the ability to incorporate more variables into our
language than the ones defined using the `,` constructor.

```maude

fmod IMP-DATA is
  pr IMP-LIST .
  sort Id .
  op a  :    -> Id [ctor metadata "16"] .
  op b  :    -> Id [ctor metadata "17"] .
  op c  :    -> Id [ctor metadata "18"] .
  op i  :    -> Id [ctor metadata "19"] .
  op j  :    -> Id [ctor metadata "20"] .
  op k  :    -> Id [ctor metadata "21"] .
  op x  :    -> Id [ctor metadata "22"] .
  op y  :    -> Id [ctor metadata "23"] .
  op z  :    -> Id [ctor metadata "24"] .
  op _, : Id -> Id [ctor metadata "25"] .
endfm

fmod IMP-DATA+MUL is
  pr IMP-DATA .
  pr FVP-NAT-MULT .
endfm

```

Here we define the syntax of IMP. We provide a simple yet expressive imperative
language syntax, including the `if - else` conditional, `while` loops, variable
assignments, basic arithmetic operations, and basic boolean operations. We also
added list expressions consisting of list assignments, list concatenation, `first`,
`last`, and `empty`. These correspond to the `head`, `tail`, and `isEmpty`
operations in our theory of lists.

```maude

fmod IMP-SYNTAX is
  pr IMP-DATA .
  sort LExp AExp BExp Exp Stmt Ids Value .
  subsort Id Nat < AExp .
  subsort Id List < LExp .
  subsort Bool < BExp .
  subsort BExp AExp LExp < Exp .
  subsort Bool Nat List < Value < Exp .

  --- ctors
  op __              : Stmt Stmt      -> Stmt  [ctor prec 42 gather (E e) metadata "26"] .
  op if (_) _ else _ : BExp Stmt Stmt -> Stmt  [ctor metadata "27" ] .
  op while (_) _     : BExp Stmt      -> Stmt  [ctor metadata "28"] .
  op {_}             : Stmt           -> Stmt  [ctor metadata "29"] .
  op {}              :                -> Stmt  [ctor metadata "30"] .
  op _=_;            : Id AExp        -> Stmt  [ctor metadata "31"] .
  op _=l_;           : Id LExp        -> Stmt  [ctor metadata "32"] .
  op _+:_            : AExp AExp      -> AExp  [ctor metadata "33"] .
  op _-:_            : AExp AExp      -> AExp  [ctor metadata "34"] .
  op _*:_            : AExp AExp      -> AExp  [ctor metadata "35"] .
  op !_              : BExp           -> BExp  [ctor metadata "36"] .
  op _<:_            : AExp AExp      -> BExp  [ctor metadata "37"] .
  op _&&:_           : BExp BExp      -> BExp  [ctor metadata "38"] .
  op _++list_        : LExp LExp      -> LExp  [ctor metadata "39"] .
  op first (_)       : LExp           -> LExp  [ctor metadata "40"] .
  op last  (_)       : LExp           -> LExp  [ctor metadata "41"] .
  op empty (_)       : LExp           -> BExp  [ctor metadata "42"] .
  op val?            : Exp            -> Bool [metadata "43"] .
  var A A' : AExp . var B B' : BExp . var L L' : LExp .
  eq val?(Q:Id)        = false [variant] .
  eq val?(A +: A')     = false [variant] .
  eq val?(A *: A')     = false [variant] .
  eq val?(A -: A')     = false [variant] .
  eq val?(! B)         = false [variant] .
  eq val?(A <: A')     = false [variant] .
  eq val?(B &&: B')    = false [variant] .
  eq val?(L ++list L') = false [variant] .
  eq val?(first(L))    = false [variant] .
  eq val?(last(L))     = false [variant] .
  eq val?(empty(L))    = false [variant] .
  eq val?(V:Value)     = true  [variant] .
endfm

fmod IMP-SYNTAX+MUL is
  pr IMP-SYNTAX .
  pr IMP-DATA+MUL .
endfm

```

The following module defines contexts for our semantic rules; this will be
covered in more detail in the semantics module.

```maude

fmod IMP-HOLE-SYNTAX is
  pr IMP-SYNTAX .
  sort !AExp !BExp !LExp !Stmt .
  --- !AExp
  op []+:_  : AExp -> !AExp [ctor metadata "44"] .
  op _+:[]  : AExp -> !AExp [ctor metadata "45"] .
  op []*:_  : AExp -> !AExp [ctor metadata "46"] .
  op _*:[]  : AExp -> !AExp [ctor metadata "47"] .
  op []-:_  : AExp -> !AExp [ctor metadata "48"] .
  op _-:[]  : AExp -> !AExp [ctor metadata "49"] .
  --- !BExp
  op ![]    : -> !BExp         [ctor metadata "50"] .
  op []<:_  : AExp -> !BExp    [ctor metadata "51"] .
  op _<:[]  : Nat -> !BExp     [ctor metadata "52"] .
  op []&&:_ : BExp -> !BExp    [ctor metadata "53"] .
  op empty([]) : -> !BExp      [ctor metadata "53"] .
  --- !LExp
  op []++list_ : LExp -> !LExp    [ctor metadata "54"] .
  op _++list[] : LExp -> !LExp    [ctor metadata "55"] .
  op first([]) : -> !LExp    [ctor metadata "56"] .
  op last([])  : -> !LExp    [ctor metadata "57"] .
  --- !Stmt
  op if ([]) _ else _ : Stmt Stmt -> !Stmt [ctor metadata "58"] .
  op while ([]) _     : Stmt      -> !Stmt [ctor metadata "59"] .
  op _=[];            : Id        -> !Stmt [ctor metadata "60"] .
  op _=l[];           : Id        -> !Stmt [ctor metadata "500"] .
endfm

```

The environment represents the state of an IMP program.
It is essentially a mapping between identifiers used in the program to
their corresponding typed value. This is achieved by having two
sub-environments. The first, referred to as `TEnv`, maps identifiers to types.
The second, referred to as `VEnv`, maps identifiers to values. The semantic
rules enforce that type safety is maintained, i.e., the value in `VEnv`
belongs to the type specified in `TEnv` associated with an identifier.


```maude

fmod ENVIRONMENT is
  pr IMP-DATA .
  sort Env .
  sort VEnv TEnv WrappedEnv .
  sort Type .
  --- Type
  op TNat   : -> Type [ctor metadata "46"] .
  op TList  : -> Type [ctor metadata "47"] .

  --- Env
  op _*_    : TEnv TEnv -> TEnv [ctor prec 51 assoc comm id: mtTE metadata "48"] .
  op _*_    : VEnv VEnv -> VEnv [ctor prec 51 assoc comm id: mtVE metadata "49"] .
  op _|->_  : Id Nat  -> VEnv [ctor prec 50 metadata "50"] .
  op _|->_  : Id List -> VEnv [ctor prec 50 metadata "51"] .
  op _|->_  : Id Type -> TEnv [ctor prec 50 metadata "52"] .
  op _&_    : TEnv VEnv -> Env [ctor metadata "53"] .
  op mt     : -> Env [ctor metadata "54"] .
  op mtVE   : -> VEnv [ctor metadata "55"] .
  op mtTE   : -> TEnv [ctor metadata "56"] .
  op {_}    : Env -> WrappedEnv [ctor metadata "57"] .
endfm

mod IMP-FVP-FRAGMENT is
  pr IMP-HOLE-SYNTAX .
  pr ENVIRONMENT .

  sort RedContext Continuation Redex .
  subsort Stmt Exp !LExp !AExp !BExp !Stmt < Redex .

  --- RedContext
  op <_|_>  : Continuation Env -> RedContext [ctor metadata "58"] .
  --- Continuation
  op _~>_   : Redex Continuation -> Continuation [ctor prec 43 metadata "59"] .
  op done   : -> Continuation [ctor metadata "60"] .
endm

```

The Semantics of IMP
====================

The semantics are in context-redex style, which
will be explained below.

```maude

mod IMP-SEMANTICS is
  pr IMP-FVP-FRAGMENT .
  pr IMP-SYNTAX .
  pr IMP-SYNTAX+MUL .

  var K : Continuation .
  var E : Env .
  var TE : TEnv .
  var VE : VEnv .
  var TY : Type .
  var S S' : Stmt .
  var Q : Id .
  var BE BE' : BExp .
  var AE AE' : AExp .
  var LE LE' : LExp .
  var N M X Y X' : Nat .
  var B : Bool .
  var L L' : List .

```

Heating Rules
-------------

Heating rules are special rules of the form

```

 A * B => A ~> [] * B

 A + B => A ~> [] + B
```

Here, the two heating rules for `*` and `+` pull out the first subexpression,
symbolically referred to as `A`, from the full expression and marks it ready for
further evaluation. The following is an example for the expression `(X + Y) *
Z)`:

```

(X + Y) * Z => X + Y ~> [] * Z => X ~> [] + Y ~> [] * Z

```

After a sequence of subexpressions have been heated and evaluated until they
cannot be further evaluated, the cooling rules take over as explained below.


```maude
  --- Rules
  --- Heating Rules
 crl [#if]        : < if (BE) S else S' ~> K | E >  => < BE ~> if ([]) S else S' ~> K | E > if val?(BE) = false .
 crl [#assign-ae] : < (Q = AE ;) ~> K | E >         => < AE ~> Q = [];    ~> K | E >        if val?(AE) = false .
 crl [#assign-le] : < (Q =l LE ;) ~> K | E >         => < LE ~> Q =l [];    ~> K | E >        if val?(LE) = false .
 crl [#add-lft]   : < AE +:  AE' ~> K | E >         => < AE ~> [] +: AE'  ~> K | E >        if val?(AE) = false .
 crl [#add-rght]  : < N  +:  AE  ~> K | E >         => < AE ~> N  +: []   ~> K | E >        if val?(AE) = false .
 crl [#mul-lft]   : < AE *:  AE' ~> K | E >         => < AE ~> [] *: AE'  ~> K | E >        if val?(AE) = false .
 crl [#mul-rght]  : < N  *:  AE  ~> K | E >         => < AE ~> N  *: []   ~> K | E >        if val?(AE) = false .
 crl [#sub-lft]   : < AE -:  AE' ~> K | E >         => < AE ~> [] -: AE'  ~> K | E >        if val?(AE) = false .
 crl [#sub-rght]  : < N  -:  AE  ~> K | E >         => < AE ~> N  -: []   ~> K | E >        if val?(AE) = false .
 crl [#and]       : < BE &&: BE' ~> K | E >         => < BE ~> [] &&: BE' ~> K | E >        if val?(BE) = false .
 crl [#lt-lft]    : < AE <:  AE' ~> K | E >         => < AE ~> [] <: AE'  ~> K | E >        if val?(AE) = false .
 crl [#lt-rght]   : < N  <:  AE  ~> K | E >         => < AE ~> N  <: []   ~> K | E >        if val?(AE) = false .
 crl [#not]       : < ! BE       ~> K | E >         => < BE ~> ! []       ~> K | E >        if val?(BE) = false .
 crl [#list-conc-left] : < LE ++list LE' ~> K | E >      => < LE ~> [] ++list LE' ~> K | E >     if val?(LE) = false .
 crl [#list-conc-rght] : < LE' ++list LE ~> K | E >      => < LE ~> LE' ++list [] ~> K | E >     if val?(LE) = false .
 crl [#list-first] : < first(LE)         ~> K | E >      => < LE ~> first([])     ~> K | E >     if val?(LE) = false .
 crl [#list-last]  : < last(LE)          ~> K | E >      => < LE ~> last([])      ~> K | E >     if val?(LE) = false .
 crl [#list-empty] : < empty(LE)         ~> K | E >      => < LE ~> empty([])     ~> K | E >     if val?(LE) = false .

 ```

Cooling Rules
-------------

Cooling rules are of the form

```

A ~> [] + B => A + B
A ~> [] * B => A + B

```

The cooling rules apply when a subexpression has cannot be heated any further,
as in the following example:

```

1 ~> [] + 2 ~> [] * 3 => 1 + 2 ~> [] * 3 => 3 ~> [] * 3 ~> 3 * 3 => 9

```

Cooling rules are useful for evaluation, as the most heated expression is
evaluated and cooled back into its parent expression for further evaluation as
seen in the example.


```maude

  --- Cooling Rules
  rl [@if]        : < B  ~> if ([]) S else S' ~> K | E > => < if (B) S else S' ~> K | E > .
  rl [@assign-ae] : < N  ~> Q = [];   ~> K | E >     => < (Q = N ;) ~> K | E > .
  rl [@assign-le] : < L  ~> Q =l [];   ~> K | E >     => < (Q =l L ;) ~> K | E > .
  rl [@add-lft]   : < N  ~> [] +: AE  ~> K | E >     => < N  +: AE  ~> K | E > .
  rl [@add-rght]  : < M  ~> N  +: []  ~> K | E >     => < N  +: M   ~> K | E > .
  rl [@mul-lft]   : < N  ~> [] *: AE  ~> K | E >     => < N  *: AE  ~> K | E > .
  rl [@mul-rght]  : < M  ~> N  *: []  ~> K | E >     => < N  *: M   ~> K | E > .
  rl [@sub-lft]   : < N  ~> [] -: AE  ~> K | E >     => < N  -: AE  ~> K | E > .
  rl [@sub-rght]  : < M  ~> N  -: []  ~> K | E >     => < N  -: M   ~> K | E > .
  rl [@and]       : < B  ~> [] &&: BE ~> K | E >     => < B &&: BE  ~> K | E > .
  rl [@lt-lft]    : < N  ~> [] <: AE  ~> K | E >     => < N <: AE   ~> K | E > .
  rl [@lt-rght]   : < M ~> N  <: []   ~> K | E >     => < N <: M    ~> K | E > .
  rl [@not]       : < B  ~> ! []      ~> K | E >     => < ! B       ~> K | E > .
  rl [@list-conc-left]  : < L  ~> [] ++list LE  ~> K | E >  => < L ++list LE ~> K | E > .
  rl [@list-conc-rght]  : < L  ~> LE ++list []  ~> K | E >  => < LE ++list L ~> K | E > .
  rl [@list-first]      : < L  ~> first([])     ~> K | E >  => < first(L)    ~> K | E > .
  rl [@list-last]       : < L  ~> last([])      ~> K | E >  => < last(L)     ~> K | E > .
  rl [@list-empty]      : < L  ~> empty([])     ~> K | E >  => < empty(L)    ~> K | E > .
  --- Semantic Rules
  --- Stmts
  rl [stmtlist]  : < S S' ~> K | E >                 => < S ~> S' ~> K | E > .
  rl [block]     : < {S} ~> K | E >                  => < S ~> K | E > .
  rl [emp-block] : < {}  ~> K | E >                  => < K | E > .
  rl [if-true]   : < if (true) S else S' ~> K | E >  => < S  ~> K | E > .
  rl [if-false]  : < if (false) S else S' ~> K | E > => < S' ~> K | E > .
  rl [while]     : < while (BE) {S} ~> K | E >       => < if (BE) {S while (BE) {S}} else {} ~> K | E > .

```

Assignment and Lookup Rules
---------------------------

To enforce type saftey, the following four rules provide the semantics of
variable assignment and lookup. The interesting point here is that for variable
lookup, the sort `Id` is used to represent two types. However, we can return a
value of the correct type by checking that the type associated with the
identifier in the `TEnv` is the same as the type of the value in the `VEnv`.
Otherwise we are in an inconsisent state, no rules will apply, and execution
will halt.

```maude
  --- Assignemnt/lookup rules assume memory locations exist and are unique
  rl [assign-nat]    : < (Q = N ;) ~> K | (TE * (Q |-> TNat)) & (VE * (Q |-> M)) >  => < K | (TE * (Q |-> TNat)) & (VE * (Q |-> N)) > .
  rl [assign-list]   : < (Q =l L ;) ~> K | (TE * (Q |-> TList)) & (VE * (Q |-> L')) >  => < K | (TE * (Q |-> TList)) & (VE * (Q |-> L)) > .
  rl [lookup-nat]    : < Q ~> K | (TE * (Q |-> TNat)) & (VE * (Q |-> N)) >          => < N ~> K | (TE * (Q |-> TNat)) & (VE * (Q |-> N)) > .
  rl [lookup-list]   : < Q ~> K | (TE * (Q |-> TList)) & (VE * (Q |-> L)) >          => < L ~> K | (TE * (Q |-> TList)) & (VE * (Q |-> L)) > .
  --- Exps
  rl [add]        : < N +: M       ~> K | E >        => < N + M        ~> K | E > .
  rl [mul]        : < N *: M       ~> K | E >        => < N * M        ~> K | E > .
  rl [sub]        : < N -: M       ~> K | E >        => < sd(N,M)      ~> K | E > .
  rl [lt]         : < N <: M       ~> K | E >        => < N < M        ~> K | E > .
  rl [not-1]      : < ! true       ~> K | E >        => < false        ~> K | E > .
  rl [not-2]      : < ! false      ~> K | E >        => < true         ~> K | E > .
  rl [and-true]   : < true  &&: BE ~> K | E >        => < BE           ~> K | E > .
  rl [and-false]  : < false &&: BE ~> K | E >        => < false        ~> K | E > .
  rl [list-conc]  : < L ++list L'  ~> K | E >        => < L $ L'       ~> K | E > .
  rl [list-first] : < first(L)     ~> K | E >        => < head(L)      ~> K | E > .
  rl [list-last]  : < last(L)      ~> K | E >        => < tail(L)      ~> K | E > .
  rl [list-empty] : < empty(L)     ~> K | E >        => < isEmpty(L)   ~> K | E > .
endm

mod NONSEQ-IMP-SEMANTICS is
  pr IMP-SEMANTICS .

  var AE AE' : AExp .
  var E : Env .
  var N : Nat .
  var K : Continuation .

 crl [@add-rght] : < AE +: AE' ~> K | E >         => < AE' ~> AE +: []   ~> K | E > if val?(AE) = false .
  rl [#add-rght] : < N  ~> AE +: []   ~> K | E >  => < AE +: N  ~> K | E > .
endm

```

