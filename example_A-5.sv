
// Example A-5 Systemverilog concurrent assertion syntax

concurrent_assertion_statement ::=
    assert property (property_spec) action_block

prperty_spec ::=
    [ clocking_event ] [ disable iff (expression_or_dist) ]
        property_expr

action_block ::=
        pass_statement_or_null
        | [ pass_statement ] else fail_statement

