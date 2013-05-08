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

one sig Timeout , Pace, Sense, Recovery, Sensing extends PMStatus {} 

sig State
{ pm : PM }

// Set initial state set for TS. We assume initially pacemaker is in SensingAPulse state
fact {
	pm.s.Sensing in initialState
}

fact {	no disj s, s': State | some s.pm & s'.pm}

// ASense becomes true between SensingAPulse and ARecovery
pred SafeASense {
	CTL_MC[Ex_BT[pm.s.Sense,pm.s.Sensing,pm.s.Recovery]]
}

// APace becomes true between SensingAPulse and ARecovery
pred SafeAPace {
	CTL_MC[Ex_BT[pm.s.Pace,pm.s.Sensing,pm.s.Recovery]]
}

// ASensingTimeout becomes true between SensingAPulse and ARecovery
pred SafeASensingTimeout {
	CTL_MC[Ex_BT[pm.s.Timeout,pm.s.Sensing,pm.s.Recovery]]
}

// APace is preceded by Timeout and it occurs between SensingAPulse and ARecovery
// SensingAPulse => Timeout => APace => ARecovery
pred SafeAPace2{
	CTL_MC[Pre_BT[pm.s.Pace,pm.s.Timeout,pm.s.Sensing,pm.s.Recovery] ]
}

// ASense is responded by ARecovery
pred SenseToRecovery {
//	CTL_MC[Res_G[pm.s.Sense,pm.s.Recovery]]
	all s' : State | s' in Res_G[pm.s.Sense,pm.s.Recovery]
}

// Response to Sensing is either Sense or Timeout
pred SensingToSenseOrTimeout {
//	CTL_MC[ Res_G[pm.s.Sensing,or_ctl[pm.s.Sensing,pm.s.Timeout]] ]
	all s' : State | s' in 	Res_G[pm.s.Sensing,or_ctl[pm.s.Sensing,pm.s.Timeout]]
}

//  Response to Timeout is Pace
pred TimeoutToPace {
//	CTL_MC[ Res_G[pm.s.Timeout,pm.s.Pace] ]
	all s' : State | s' in Res_G[pm.s.Timeout,pm.s.Pace]
}

//  Response to Pace is Recovery
pred PaceToRecovery {
//	CTL_MC[ Res_G[pm.s.Pace,pm.s.Recovery] ]
	all s' : State | s' in Res_G[pm.s.Pace,pm.s.Recovery]
}

//  Response to Recovery is Sensing
pred RecoveryToSensing {
//	 CTL_MC[ Res_G[pm.s.Recovery,pm.s.Sensing] ]
	all s' : State | s' in Res_G[pm.s.Recovery,pm.s.Sensing]
}

//  Response to Sense is not  Pace until the next Sensing
pred SenseToNotPace {
//	 CTL_MC[ Res_G[pm.s.Recovery,pm.s.Sensing] ]
	all s' : State | s' in Res_B[pm.s.Sense,not_ctl[pm.s.Pace],pm.s.Sensing]
}

pred StayInSameStatus {
//	all s' : State | s' in implies_ctl[s', EX[s']]
}


pred Generate {}

fact{
--	SafeASense
--	SafeAPace
--	SafeAPace2
--	SafeASensingTimeout
	SenseToRecovery
	SensingToSenseOrTimeout
	TimeoutToPace
	PaceToRecovery
	RecoveryToSensing
	StayInSameStatus
	SenseToNotPace
}


run Generate for 10

