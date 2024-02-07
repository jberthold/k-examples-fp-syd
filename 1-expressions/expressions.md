# A little expression language definition in K

K definitions can be written in plain files or in markdown as
demonstrated here. When using markdown, the code parts have to be
enclosed in code blocks starting with ` ```k `

```k
module EXPRESSIONS-SYNTAX
```

A _definition_ in K consists of a number of _modules_, with a dedicated _main module_ and another _main syntax module_. The main module is by default the file name of the definition capitalised. The main syntax module is by default the main module with suffix `-SYNTAX`.
The main syntax module (unsurprisingly) defines the syntax while the main module defines the semantics (in terms of rewrite rules).

```k
    // we import built-in INT and BOOL syntax
    imports INT-SYNTAX
    imports BOOL-SYNTAX

    syntax Exp ::= Int | Bool
               | "(" Exp ")" [bracket]

    // Integer arithmetic syntax
               > non-assoc:
                  "-" Exp     [color(violet),seqstrict]
               > left:
                  Exp "*" Exp [color(violet),seqstrict]
               |  Exp "/" Exp [color(violet),strict]
               > left:
                  Exp "+" Exp [color(violet),strict]
               |  Exp "-" Exp [color(violet),seqstrict]
    // Integer comparison syntax
               > non-assoc:
                  Exp "<"  Exp [color(teal),seqstrict]
               |  Exp "<=" Exp [color(teal),seqstrict]
               |  Exp ">"  Exp [color(teal),seqstrict]
               |  Exp ">=" Exp [color(teal),seqstrict]
    // comparison for both Bool and Int
               |  Exp "==" Exp [color(teal),seqstrict]
               |  Exp "!=" Exp [color(teal),seqstrict]
    // Bool operators
               > left:
                  "!" Exp [color(blue),seqstrict]
               > left:
                  Exp "&&" Exp [color(blue),seqstrict]
                | Exp "^"  Exp [color(blue),seqstrict]
                | Exp "||" Exp [color(blue),seqstrict]
                | Exp "->" Exp [color(blue),seqstrict]

endmodule
```

```k
module EXPRESSIONS
    imports EXPRESSIONS-SYNTAX
    imports INT
    imports BOOL

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

endmodule
```
