open util/integer
open temporal_logics/ctl_2[State]
open temporal_logics/ctl_patterns[State]

/*
 * Atria APacemaker TS graph
digraph APacemaker {
  node [shape="circle"  fixedsize=true ];
  ASensingAPulse -> AASensingATimeout;
  ASensingAPulse -> AASense;
  ASensingATimeout -> APace;
  ASense -> ARecovery;
  APace -> ARecovery;
  ARecovery -> ASensingAPulse;
}
*/

sig ID {}

sig PM {
  id : ID,
  s : PMStatus,
  mode: PMMode,
  f: some PMFeature
}

abstract sig PMStatus  {}

abstract sig PMMode  {}

abstract sig PMFeature {}

one sig F_APacing, F_VPacing extends PMFeature {}


// one sig ATimeout, APace, ASense, ARecovery, ASensing, VTimeout, VPace, VSense, VRecovery, VSensing extends PMStatus {} 
one sig APace, ARecovery, VPace, VRecovery extends PMStatus {} 

one sig DOO, AOO, VOO extends PMMode{}

sig State
{ pm : PM }

// Set initial state set for TS. We assume initially pacemaker is in ASensingAPulse state
fact {
	pm.s.APace in initialState
}

// Structural constraints
fact {
  // Activate features depending on the mode
  all p': PM | p'.mode = AOO => (F_APacing = p'.f)
  all p': PM | p'.mode = VOO => (F_VPacing = p'.f)
  all p': PM | p'.mode = DOO => ((F_VPacing+F_APacing) = p'.f)
}

// VPacing constraints
fact {
	all p': PM | F_VPacing not in p'.f => VPace not in p'.s
}

// APacing constraints
fact {
	all p': PM | F_APacing not in p'.f => APace not in p'.s
}


// One-to-one mapping between state and pacemaker
fact {	no disj s, s': State | some s.pm & s'.pm}

pred SafeAPacing{
  // Atria pacing constraints
  // ARecovery responds to APace
  all s' : State | s'.pm.f=F_APacing => s' in Res_G[pm.s.APace,pm.s.ARecovery]
}

pred SafeVPacing{
  // Ventricle pacing constraints
  // VRecovery responds to VPace
  all s' : State | s'.pm.f=F_VPacing => s' in Res_G[pm.s.VPace,pm.s.VRecovery]
}

pred SafeAVPacing{
  // Dual pacing constraints
  // APace is followed by VPace in
  all s' : State | s'.pm.f=(F_APacing + F_VPacing) => s' in Ex_BT[pm.s.VPace, pm.s.ARecovery,pm.s.VRecovery]
  all s' : State | s'.pm.f=(F_APacing + F_VPacing) => s' in Ex_BT[pm.s.APace, pm.s.VRecovery,pm.s.ARecovery]
}

pred SafeModeSwitching{
	// Mode can only be changed during VRecovery or ARecovery
  all s' : State | s' in pm.s.ARecovery or s' in pm.s.VRecovery or (s' in and_ctl[pm.mode.AOO,AX[pm.mode.AOO]] or s' in and_ctl[pm.mode.DOO,AX[pm.mode.DOO]] or s' in and_ctl[pm.mode.VOO,AX[pm.mode.VOO]] )
}

pred SafeNoVEventsInAModes{
	// If there are no V Features, VRecovery is not visited
	// this is a structural constraint
  all s' : State | s'.pm.f != F_VPacing => s' not in pm.s.VRecovery
}

pred SafeNoAEventsInVModes{
	// If there are no Atria Features, ARecovery is not visited
	// this is a structural constraint
  all s' : State | s'.pm.f != F_APacing => s' not in pm.s.ARecovery
}

pred Generate {}

fact{
  SafeAPacing
  SafeVPacing
  SafeAVPacing
  SafeModeSwitching
  SafeNoVEventsInAModes
  SafeNoAEventsInVModes
}


run Generate for 10 but 1 ID 

