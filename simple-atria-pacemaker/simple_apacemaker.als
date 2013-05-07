open util/integer
open temporal_logics/ctl[State]

/*
 * Atria Pacemaker TS graph
digraph APacemaker {
  node [shape="circle"  fixedsize=true ];
  SensingAPulse -> ASensingTimeout;
  SensingAPulse -> ASense;
  ASensingTimeout -> APace;
  ASense -> ARecovery;
  APace -> ARecovery;
  ARecovery -> SensingAPulse;
}
*/

sig ID {}

sig PM {id : ID, s : one PMStatus}

abstract sig PMStatus  {}

one sig ASensingTimeout , APace, ASense, ARecovery, SensingAPulse extends PMStatus {} 

sig State
{ pm : PM }

// Set initial state set for TS. We assume initially pacemaker is in SensingAPulse state
fact {
	pm.s.SensingAPulse in initialState
}

fact {	no disj s, s': State | some s.pm & s'.pm}

// ASensingTimeout is eventually followed by ASense or ASensingTimeout
// AG(SensingAPulse => AF(ASense or ASensingTimeout))
pred SafeSensing {
	CTL_MC[AG[implies_ctl[pm.s.SensingAPulse, AF[or_ctl[pm.s.ASense,  pm.s.ASensingTimeout]  ] ] ] ]
}

// ASense is eventually followed by ARecovery
// AG(ASense => AF(ARecovery))
pred SafeSense{
	CTL_MC[AG[implies_ctl[pm.s.ASense, AF[pm.s.ARecovery] ] ] ]
}

// ASensingTimeout is eventually followed by APace
// AG(ASensingTimeout => AF(APace))
pred SafeTimeout{
	CTL_MC[AG[implies_ctl[pm.s.ASensingTimeout, AF[pm.s.APace ]]  ] ] 
}

// APace is eventually followed by ARecovery
// AG(APace => AF(ARecovery))
pred SafePace{
	CTL_MC[AG[implies_ctl[pm.s.APace, AF[pm.s.ARecovery] ] ] ]
}

// ARecovery is eventually followed by SensingAPulse
// AG(ARecovery => AF(SensingAPulse))
pred SafeRecovery{
	CTL_MC[AG[implies_ctl[pm.s.ARecovery, AF[pm.s.SensingAPulse] ] ] ]
}

fact{
	SafeSense
	SafeTimeout
	SafePace
	SafeRecovery
}


run SafeSensing

/*
assert MC{
	CTL_MC[not_ctl[ AG[implies_ctl[pm.s.SensingAPulse, or_ctl[AX[pm.s.ASense],  AX[pm.s.ASensingTimeout]]  ] ] ]  ]
	CTL_MC[not_ctl[ AG[implies_ctl[pm.s.ASensingTimeout, AX[pm.s.APace] ] ] ]  ]
	CTL_MC[not_ctl[ AG[implies_ctl[pm.s.APace, AX[pm.s.ARecovery] ] ] ]  ]
	CTL_MC[not_ctl[ AG[implies_ctl[pm.s.ASense, AX[pm.s.ARecovery] ] ] ]  ]
}
check MC for 10 State, 10 PM, 4 ID, 10 PMStatus
*/
/*
pred aaa {
	CTL_MC[not_ctl[ AG[implies_ctl[pm.s.SensingAPulse, or_ctl[AX[pm.s.ASense], AX[pm.s.ASensingTimeout]] ] ] ] ]
}
*/
