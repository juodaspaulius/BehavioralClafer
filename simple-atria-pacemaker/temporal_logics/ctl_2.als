module temporal_logics/ctl_2[S]

private one sig TS{
	S0: some S,
	sigma: S -> S
}

fun initialState: S { TS.S0 }

fun nextState: S -> S{ TS.sigma }

// Every state has some next state:
fact {S = TS.sigma.S}

// Helper functions for model checking

private fun bound[R:S->S,X:S]
:S->S{
  X <: R
}

private fun id[X:S]
:S->S{
  bound[iden,X]
}

private fun loop[R: S->S]
:S{
  S.(^R & id[S])
}

// Temporal connectives of CTL

fun not_ctl[phi:S]:S { S - phi }

fun and_ctl[phi,si:S]:S { phi & si }

fun or_ctl[phi,si:S]:S { phi + si }

fun implies_ctl[phi,si:S]:S { not_ctl[phi] + si }

fun EX[phi:S]:S {TS.sigma.phi }

fun AX[phi:S]:S {not_ctl[EX[not_ctl[phi]]] }

fun EF[phi:S]:S { (*(TS.sigma)).phi }

fun AF[phi:S]:S {not_ctl[EG[not_ctl[phi]]]}

fun EG[phi:S]:S { let R= bound[TS.sigma,phi] | (*R).(loop[R]) }

fun AG[phi:S]:S { not_ctl[EF[not_ctl[phi]]] }

fun EU[phi,si:S]:S {(*(bound[TS.sigma,phi])).si}

fun AU[phi,si:S]:S {not_ctl[or_ctl[EG[not_ctl[si]],EU[not_ctl[si],not_ctl[or_ctl[phi,si]]]]]}

fun EW[phi,si:S]:S {not_ctl[AU[and_ctl[phi,not_ctl[si]],and_ctl[not_ctl[phi],not_ctl[si]]]]}

fun AW[phi,si:S]:S {not_ctl[EU[and_ctl[phi,not_ctl[si]],and_ctl[not_ctl[phi],not_ctl[si]]]]}

// model checking constraint

pred CTL_MC[phi:S]{
	TS.S0 in phi
}
