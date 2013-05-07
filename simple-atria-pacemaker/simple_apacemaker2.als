open util/integer
open temporal_logics/ctl_2[State]
open temporal_logics/ctl_patterns[State]

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

// ASense becomes true between SensingAPulse and ARecovery
pred SafeASense {
	CTL_MC[Ex_BT[pm.s.ASense,pm.s.SensingAPulse,pm.s.ARecovery]]
}

// APace becomes true between ASensingTimeout and ARecovery
pred SafeAPace {
	CTL_MC[Ex_BT[pm.s.APace,pm.s.ASensingTimeout,pm.s.ARecovery]]
}

// ASensingTimeout is preceded by SensingAPulse
pred SafeASensingTimeout {
	CTL_MC[Pre_G[pm.s.ASensingTimeout,pm.s.SensingAPulse]]
}

// SensingAPulse is a response to ARecovery
pred SafeSensingAPulse {
	CTL_MC[Res_G[pm.s.SensingAPulse,pm.s.ARecovery]]
}

fact{
	SafeASense
	SafeAPace
	SafeASensingTimeout
}


run SafeSensingAPulse for 10

