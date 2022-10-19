requires "../2-variables/variables.k"

module FUNCTIONS-SYNTAX
    imports VARIABLES-SYNTAX
    imports ID-SYNTAX

    // Function declarations
    syntax Decls ::= NeList{Decl, ""}

    syntax Decl ::= Id "(" Params ")" "=" Body

    syntax Params ::= List{Id, ","}

    syntax Body ::= Exp

    syntax Id ::= "main" [token]

    // function call
    syntax Exp ::= Id "(" Args ")"

    syntax Args ::= List{Exp, ","}

endmodule

module FUNCTIONS
    imports FUNCTIONS-SYNTAX
    imports INT
    imports BOOL
    imports ID
    imports MAP
    imports LIST

    configuration
      <T>
        <k> $PGM:Decls </k>    // process declarations, then execute main
        <store> .Map </store> // stores bound variables
        <args> .Map </args> // helper store for function arguments
        <functions> .Map </functions> // stores function declarations
        <call-stack> .List </call-stack> // stores continuations
      </T>

    // technicality to make the `seqstrict` above work
    syntax Bool ::= isKResult(K) [function, symbol]
    rule isKResult(_:Int)  => true
    rule isKResult(_:Bool) => true
    rule isKResult(_)      => false [owise]

    // semantics of Int and Bool expressions
    rule <k> - I1:Int => 0 -Int I1 ... </k>
    rule <k> I1:Int + I2:Int => I1 +Int I2 ...</k>
    rule <k> I1:Int - I2:Int => I1 -Int I2 ...</k>
    rule <k> I1:Int * I2:Int => I1 *Int I2 ...</k>
    rule <k> I1:Int / I2:Int => I1 /Int I2 ...</k> requires I2 =/=Int 0

    rule <k> ! B1:Bool          => notBool B1 ...</k>
    rule <k> B1:Bool && B2:Bool => B1 andBool B2 ...</k>
    rule <k> B1:Bool ^ B2:Bool  => B1 xorBool B2 ...</k>
    rule <k> B1:Bool || B2:Bool => B1 orBool B2 ...</k>
    rule <k> B1:Bool -> B2:Bool => B1 impliesBool B2 ...</k>

    // comparison operators for `Int` (returning `Bool`)

    rule <k> I1:Int <  I2:Int => I1 <Int I2 ...</k>
    rule <k> I1:Int <= I2:Int => I1 <=Int I2 ...</k>
    rule <k> I1:Int >  I2:Int => I1 >Int I2 ...</k>
    rule <k> I1:Int >= I2:Int => I1 >=Int I2 ...</k>
    rule <k> I1:Int == I2:Int => I1 ==Int I2 ...</k>
    rule <k> I1:Int != I2:Int => I1 =/=Int I2 ...</k>

    // with `==` and `!=`, we _should_ be able to compare `Bool`.
    rule <k> B1:Bool == B2:Bool => B1 ==Bool B2 ...</k>
    rule <k> B1:Bool != B2:Bool => B1 =/=Bool B2 ...</k>

    rule <k> X:Id => V ... </k>
         <store> ... X |-> V ... </store>

    rule <k> let X:Id = V in E => E </k>
         <store> M => M [ X <- V ] </store>
      requires notBool (X in_keys(M)) andBool isKResult(V)

    rule <k> B:Bool ? E : _ => E ...</k>
         requires B
    rule <k> B:Bool ? _ : E => E ...</k>
         requires notBool B

    // store function declarations (startup)
    rule <k> F ( Ps:Params ) = EBody:Exp => . ... </k>
         <functions> M => M [ F <- #decl(Ps, EBody) ] </functions>
         requires notBool (F in_keys(M))

    // process all declarations in order
    rule <k> D:Decl DD:Decls ~> Rest => D ~> DD ~> Rest </k>

    // execute main afterwards
    rule <k> .Decls => main(.Args) ~> . </k>

    // function setup helpers
    syntax KItem ::= #state ( Map, K )
                   | #bindParams ( Params, Args )
                   | #bindParam (Id, Exp)         [strict(2)]
                   | #decl ( Params, Body )

    // function call, saving continuation and creating a local store
    // NB, arguments need to be fully evaluated using the old store
    rule <k> F ( ARGS:Args ) ~> Cont => #bindParams(Ps, ARGS) ~> EBody </k>
         <store> Store </store>
         <args> _ => .Map </args>
         <functions> ... F |-> #decl(Ps, EBody) ... </functions>
         <call-stack> Stack => ListItem(#state(Store, Cont)) Stack </call-stack>

    // construct function environment (store)
    rule <k>
           #bindParams ((P:Id, PS), (A, AS)) => #bindParam(P, A) ~> #bindParams(PS, AS)
           ...
         </k>

    rule <k> #bindParam(P, A) => . ... </k>
         <args> M => M [ P <- A ] </args>
         requires isKResult(A)

    rule <k> #bindParams(.Params , .Args) => . ...</k>
         <store> _ => ArgStore </store>
         <args> ArgStore => .Map </args>

    // function returning
    rule <k> E:Exp ~> .K => E ~> Cont </k>
         <store> _ => Store </store>
         <call-stack> ListItem(#state(Store, Cont)) Rest => Rest </call-stack>
       requires isKResult(E)

endmodule
