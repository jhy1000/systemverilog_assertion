

Examples fromthe previous sections briefly introduce the implication operator and $past() system function.
The tables below list some more useful tools that let you write assertion expressions.



//  SVA SYSTEM FUNCTIONS

$rose           : returns true if the LSB of the expression changed to 1. Otherwise, it returns false.
$fell           : returns true if the LSB of the expression changed to 0. Otherwise, it returns false.
$stable         : returns true if the value of the expression did not change. Otherwise, it returns false.

$past(expression, num_cycles)   : returns value of expression from num_cycles ago

$countones      : returns the number of 1s in an expression
$onehot         : returns true if exactly one bit is 1. if no bits or more than one bit is 1, it returns false.

$onebit0        : returns true if no bits or just 1 bit in the expression is 1

$isunknown      : returns true if any bit in the expresion is 'X' or 'Z'


// SVA OPERATOR

##n ##[m:n]     : Delay operator - Fixed time interval and Time interval range

!, ||, &&       : Boolean operator

|->             : Overlapping implication

|=>             : Nonoverlapping implicaton

not, or, and    : Property operators



// Repetition operator

[*n] / [*m:n]   : Continuous repetition operator. The expression repeats continuously for the specified range of cycles.
[->n] / [->m:n] : Go to repetition opertor. Indicates there's one or more delay cycles between each repetition of the expression.
                  a[->3] is equivalent to (!a[*0:$] ##1 a) [*3]
[=n] / [=m:n]   : Non-consecutive


// NOTE: The table above lists operators most frequently used in SVAs. There are several more - intersect, throughout, within, etc. 
// In my opinion, while these operators are powerful, they lead to confusion. Most assertions can be written using the above table.


