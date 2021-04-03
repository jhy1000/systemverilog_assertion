


// Systemverilog provides syntactic sugar to simplify expressing the repetition for 
// boolean expression or a sequence expression.
//
// For example, the sequence (a ##1 a) can be expressed as sequence a[*2]
//
//
//
// The [*n] construct is used to represent a repetition, where n is a constant.
// A repetition range can be expressed using [*m:n], where both m and n are constants.
//
//
//
a [*0] ##1 b        same as (b), a is not repeated.
a [*2] ##1 b        same as (a ##1 a ##1 b)
a [*1:2] ##1 b      same as (a ##1 b)or (a ##1 a ##1 a ##1 b)
(a ##1 b) [*2]      same as (a ##1 b ##1 a ##1 b)


