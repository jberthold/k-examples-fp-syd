requires "../1-expressions/expressions.md"

module VARIABLES-SYNTAX
    imports EXPRESSIONS-SYNTAX
    imports ID-SYNTAX

    // Identifiers can be expressions
    syntax Exp ::= Id


    // syntactic construct for variables, and expression-if
    syntax Exp ::= "let" Id "=" Exp "in" Exp [strict(2)]
                  | Exp "?" Exp ":" Exp      [strict(1)]
endmodule

module VARIABLES
    imports VARIABLES-SYNTAX
    imports ID
    imports MAP

    imports INT
    imports BOOL

    configuration
      <T>
        <k> $PGM:Exp </k>    // contains expression to evaluate
        <store> .Map </store> // stores bound variables
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

endmodule
