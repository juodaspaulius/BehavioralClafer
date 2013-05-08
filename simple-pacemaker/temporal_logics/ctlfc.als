module temporal_logics/ctlfc[S]

private one sig TS{
	S0: some S,
	sigma: S -> S,
	FC1,FC2: set S
}

fun initialState: S { TS.S0 }

fun nextState: S -> S{ TS.sigma }

fun fc1: S { TS.FC1 }

fun fc2: S { TS.FC2 }

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

// The body of this function needs to be adjusted with respect
// to fairness constraints.

fun Fair: S{
	let R = TS.sigma, ids1=id[fc1], ids2=id[fc2]|
 	(*R).(loop[R] & loop[(*R).ids1.(*R).ids2.(*R)])
 }
 

// Temporal operators of CTLFC

fun not_ctlfc[phi:S]:S { S - phi }

fun and_ctlfc[phi,si:S]:S { phi & si }

fun or_ctlfc[phi,si:S]:S { phi + si }

fun implies_ctlfc[phi,si:S]:S { not_ctlfc[phi] + si }

fun ECX[phi:S]:S {TS.sigma.(phi & Fair) }

fun ACX[phi:S]:S {not_ctlfc[ECX[not_ctlfc[phi]]] }

fun ECF[phi:S]:S { (*(TS.sigma)).(phi&Fair) }

fun ACF[phi:S]:S {not_ctlfc[ECG[not_ctlfc[phi]]]}

// This one also needs to be edited in a similar way to Fair.
fun ECG[phi:S]:S { 
	let R= bound[TS.sigma,phi], ids1=id[fc1], ids2=id[fc2]|
 	(*R).(loop[R] & loop[(*R).ids1.(*R).ids2.(*R)])
}

fun ACG[phi:S]:S { not_ctlfc[ECF[not_ctlfc[phi]]] }

fun ECU[phi,si:S]:S {(*(bound[TS.sigma,phi])).(si&Fair)}

fun ACU[phi,si:S]:S {not_ctlfc[or_ctlfc[ECG[not_ctlfc[si]],ECU[not_ctlfc[si],not_ctlfc[or_ctlfc[phi,si]]]]]}

// model checking constraint

pred CTLFC_MC[phi:S]{
	TS.S0 in phi
}
