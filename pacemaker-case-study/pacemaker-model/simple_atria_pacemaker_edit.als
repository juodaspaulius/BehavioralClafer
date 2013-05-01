/*
All clafers: 6 | Abstract: 1 | Concrete: 5 | References: 0
Constraints: 0
Goals: 0
Global scope: 1..*
All names unique: False
*/
open util/integer
open temporal_logics/ctl[State]

// pred show {}
// run  show for 1 but 1 c1_PM, 1 c2_S, 1 c3_ASensingTimeout, 1 c4_APace, 1 c5_State, 1 c6_PM


sig ID {}

abstract sig c1_PM
{
	id : ID,
	S : c2_S 
}

sig c2_S
{ ASensingTimeout : lone c3_ASensingTimeout
, APace : lone c4_APace
, ASense : lone c37_ASense
, ARecovery : lone c41_ARecovery
, SensingAPulse : lone c43_SensingAPulse
 }
{ one @S.this
  let children = (ASense + APace + ARecovery + SensingAPulse + ASensingTimeout ) | one children }

sig c3_ASensingTimeout
{}
{ one @ASensingTimeout.this }

sig c4_APace
{}
{ one @APace.this }

sig c37_ASense
{}
{ one @ASense.this }

sig c41_ARecovery
{}
{ one @ARecovery.this }

sig c43_SensingAPulse
{}
{ one @SensingAPulse.this }

sig c6_PM extends c1_PM
{}

sig State
{ pm : one c6_PM }

// Want to express implication:
// AG(PM.S.ASensingTimeout => AX S.APace)

pred senseAndPace [s, s': State] {
	s.pm.id = s'.pm.id &&
	one s.pm.S.ASensingTimeout && 
	one s'.pm.S.APace 
    -- CTL_MC[AG[implies_ctl[s ,  AX[s']  ] ] ]	
}

run senseAndPace -- for 50
