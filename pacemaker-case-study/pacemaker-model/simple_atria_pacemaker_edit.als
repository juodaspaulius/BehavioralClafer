open util/integer
open temporal_logics/ctl[State]

// pred show {}
// run show for 1 but 1 c1_PM, 1 c2_S, 1 c3_ASensingTimeout, 1 c4_APace, 1 c5_State, 1 c6_PM


sig ID {}

sig PM {
id : ID,
	s : lone  PMStatus
}{
 	one this[pm]
}


abstract sig PMStatus  {}

one sig ASensingTimeout , APace, ASense, ARecovery, SensingAPulse extends PMStatus {} 

sig State
{ pm : one PM }

fact TransitionRelation {
 all s, s' : State | s' in nextState[s]
--	all s: State | one s.pm
}

fact {
	no disj s, s': State | some s.pm & s'.pm
}

assert MC{
	CTL_MC[not_ctl[ AG[implies_ctl[pm.s.SensingAPulse, or_ctl[AX[pm.s.ASense],  AX[pm.s.ASensingTimeout]]  ] ] ]  ]
--	CTL_MC[not_ctl[ AG[implies_ctl[pm.s.ASensingTimeout, AX[pm.s.APace] ] ] ]  ]
-- CTL_MC[not_ctl[ AG[implies_ctl[pm.s.APace, AX[pm.s.ARecovery] ] ] ]  ]
--	CTL_MC[not_ctl[ AG[implies_ctl[pm.s.ASense, AX[pm.s.ARecovery] ] ] ]  ]
}

check MC for 10 State, 10 PM, 4 ID, 10 PMStatus
