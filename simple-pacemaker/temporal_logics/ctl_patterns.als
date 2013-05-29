module temporal_logics/ctl_patterns[S]

open temporal_logics/ctl_2[S]

// Scopes
// More info: http://patterns.projects.cis.ksu.edu/documentation/patterns/scopes.shtml
// G - global
// B - Before R
// A - After Q
// BT - Between Q and R
// AU After Q until R

// Patterns
// More info: http://patterns.projects.cis.ksu.edu/documentation/patterns/ctl.shtml
// Abs - Absence. P is false
// Ex - Existence. P becomes true.
// Uni - Universality. P is true.
// Pre - Precedence. S precedes P.
// Res - Response. S responds to P.

// Existence
// * Between Q and R
// AG(Q & !R -> A[!R W (P & !R)])
fun Ex_BT[P1,Q1,R1:S]:S { AG[implies_ctl[and_ctl[Q1,not_ctl[R1]],AW[not_ctl[R1],and_ctl[P1,not_ctl[R1]]]]] }


// Response
// * Globally
// AG(P -> AF(S))
fun Res_G[P1,S1:S]:S {AG[implies_ctl[P1, AF[S1]]] }

// * Before R
// A[((P -> A[!R U (S & !R)]) | AG(!R)) W R]
fun Res_B[P1,S1,R1:S]:S {AW[or_ctl[implies_ctl[P1,AU[not_ctl[R1],and_ctl[S1,not_ctl[R1]]]],AG[not_ctl[R1]]],R1]}

// Precedence (P is preceded by S)
// * Globally
// A[!P W S]
fun Pre_G[P1,S1:S]:S { AW[not_ctl[P1], S1] }

// * Between Q and R
// AG(Q & !R -> A[(!P | AG(!R)) W (S | R)])
fun Pre_BT[P1,S1,Q1,R1:S]:S {AG[implies_ctl[and_ctl[Q1,not_ctl[R1]],AW[or_ctl[not_ctl[P1],AG[not_ctl[R1]]], or_ctl[S1,R1]]]]}


