requires "../4-statements/statements.k"

module VERIFICATION
    imports STATEMENTS  // other things are recursively imported
     // proof tools and helpers
    imports MAP-SYMBOLIC
    imports K-EQUAL

    syntax Id ::= "$n"      [token]
              | "$k"        [token]
              | "$sum"      [token]
              | "$sumwhile" [token]
              | "$sumrec"   [token]
              | "$main"     [token]

endmodule

module SUM-SPEC
    imports VERIFICATION

 claim [seven]:
   <k> 1 + 2 + 3 + 4 => 10
   ... </k>

 claim [assign]:
   <k> if (1 + 2 + 3 + 4 == 10) $k = 1
         else $k = 0
       => .
   ... </k>
   <store> M => M [ $k <- 1 ] </store>

 claim [reassign]:
   <k> $k = 1 + 2 + 3
       ~> $k = $k + 4
       => .
   ... </k>
   <store> .Map => .Map [ $k <- 10 ] </store>

 claim [def]:
   <k> $sumrec($n) =
         if ( $n <= 0 ) return 0
           else return ($n + $sumrec($n - 1))
       ~> $k = 1 + 2 + 3 + 4
       => .
   ... </k>
   <store> .Map => .Map [ $k <- 10 ] </store>
   <functions> .Map => ?_ </functions>

 claim [call]:
   <k> $sumrec($n) =
         if ( $n <= 0 ) return 0
           else return ($n + $sumrec($n - 1))
       ~> $k = $sumrec(4)
       => .
   ... </k>
   <store> .Map => .Map [ $k <- 10 ] </store>
   <args> .Map => ?_ </args> // comment this out for a test
   <functions> .Map => ?_ </functions>
   <call-stack> .List </call-stack>

 claim [loop]:
   <k> while ( KLoop > 0 ) {
           SLoop = SLoop + KLoop;
           KLoop = KLoop - 1
         }
     =>
     . ...
  </k>
  <store>
    _Store
    SLoop |-> (S:Int => S +Int (N *Int (N +Int 1) /Int 2))
    KLoop |-> (N:Int => 0)
  </store>
  <args> _ => ?_ </args>
  <functions> _ </functions>
  <call-stack> _ </call-stack>
  requires N >=Int 0
   andBool S >=Int 0

 claim [sum-of-n]:
   <k> $sumwhile ( $n ) = {
         $k = $n;
         $sum = 0;
         while ( $k > 0 ) {
           $sum = $sum + $k;
           $k = $k - 1
         };
         return $sum
       }
       ~> $sumwhile(N)
     =>
       N *Int (N +Int 1) /Int 2 ~> .
  </k>
  <store> .Map => ?_ </store>
  <args> .Map => ?_ </args>
  <functions> .Map => ?_ </functions>
  <call-stack> .List => ?_ </call-stack>
  requires N >=Int 0


endmodule
