/*
All clafers: 8 | Abstract: 2 | Concrete: 6 | References: 0
Constraints: 3
Goals: 0
Global scope: 1..*
All names unique: False
*/
open util/integer
open temporal_logics/ctl[c1_Person]
pred show {}
run  show for  20 but exactly 6 c1_Person

/* Clafer:
// main concept
abstract Person
	age : integer
	[ age >= 0 ]
	[ next(age) >= age ]

	xor maritalStatus
		neverMarried
		married
			[ age >= 2 ]  
		divorced
	[ neverMarried ---> married <---> divorced ]    
*/

sig c1_Person
{ r_c2_age : one c2_age
, r_c6_maritalStatus : one c6_maritalStatus, nextState: set c1_Person }
{ (this.@r_c2_age.@ref) >= 0 }

fact {	
	next = nextState

	// age increases
	all p,p':c1_Person| p' in next[p] implies p'.r_c2_age.ref >= p.r_c2_age.ref
}

sig c2_age
{ ref : one Int }
{ one @r_c2_age.this }

// NEW: [ age increases ] means that in the next step, age can stay the same or increase
// TODO: write the constraint in temp. logic.

sig c6_maritalStatus
{ r_c7_neverMarried : lone c7_neverMarried
, r_c8_married : lone c8_married
, r_c12_divorced : lone c12_divorced }
{ one @r_c6_maritalStatus.this
  let children = (r_c7_neverMarried + r_c8_married + r_c12_divorced) | one children }

sig c7_neverMarried
{}
{ one @r_c7_neverMarried.this }

sig c8_married
{}
{ one @r_c8_married.this
  (((this.~@r_c8_married).~@r_c6_maritalStatus).@r_c2_age.@ref) >= 2 }

sig c12_divorced
{}
{ one @r_c12_divorced.this }

// NEW: generated abstract states for the behavioral constraint
// [ neverMarried ---> married <---> divorced ]    
//        ^                    ^                    ^  
//        S1                  S2                   S3
  

// predicate to represent state S1 invariants
pred is_c1_Person_NeverMarried [ p : c1_Person ]
{ one p.@r_c6_maritalStatus.@r_c7_neverMarried }

// abstract state S1
sig c1_Person_S1 in c1_Person {}
fact { c1_Person_S1 = { p : c1_Person | is_c1_Person_NeverMarried [p] } }

// predicate to represent state S2 invariants
pred is_c1_Person_Married [ p : c1_Person ]
{ one  p.@r_c6_maritalStatus.@r_c8_married }

// abstract state S2
sig c1_Person_S2 in c1_Person {}
fact { c1_Person_S2 = { p : c1_Person | is_c1_Person_Married [p] } }

// predicate to represent state S3 invariants
pred is_c1_Person_Divorced [ p : c1_Person ]
{ one p.@r_c6_maritalStatus.@r_c12_divorced }

// abstract state S3
sig c1_Person_S3 in c1_Person {}
fact { c1_Person_S3 = { p : c1_Person | is_c1_Person_Divorced [p] } }

// TODO:
// write a constraint that "from being neverMarried you can become married then divorced and married and divorced... 
// but you can never become neverMarried again once you got married or divorced"

/* Clafer:
// abstract state
abstract NewBorn -> Person
	[ age = 0
	  neverMarried ]
*/

// NEW: generated abstract state

// abstract state NewBorn
sig c13_NewBorn in c1_Person {}
fact { c13_NewBorn = { p : c1_Person | is_c13_NewBorn[p] } }

// predicate to represent state NewBorn invariants
pred is_c13_NewBorn [ p : c1_Person ]      
{ ((p.@r_c2_age.@ref) = 0) && is_c1_Person_NeverMarried [p] }

/* Clafer:
// concept instance
Bob : Person
	[ NewBorn ---> married ]
*/

one sig c20_Bob extends c1_Person {}

fact {
	// Bob is the initial state: 
	first = c20_Bob 

	// Bob is a new born:
	is_c13_NewBorn[c20_Bob]
}

fact {

	// if a person is neverMarried, in the next state, he can get married:
	CTL_Formula[AG[implies_ctl[r_c6_maritalStatus.r_c7_neverMarried.c7_neverMarried,EX[r_c6_maritalStatus. r_c8_married.c8_married]]]]

	// if a person is neverMarried, in the next state, he can still be neverMarried:
	CTL_Formula[AG[implies_ctl[r_c6_maritalStatus.r_c7_neverMarried.c7_neverMarried,EX[r_c6_maritalStatus.r_c7_neverMarried.c7_neverMarried]]]]

	// if a person is neverMarried, in the next state he has to be either neverMarried or married:
	CTL_Formula[AG[implies_ctl[r_c6_maritalStatus.r_c7_neverMarried.c7_neverMarried,AX[or_ctl[r_c6_maritalStatus. r_c8_married.c8_married,r_c6_maritalStatus.r_c7_neverMarried.c7_neverMarried]]]]]

	// if a person is married, in the next state, he can get divorced:
	CTL_Formula[AG[implies_ctl[r_c6_maritalStatus.r_c8_married.c8_married,EX[r_c6_maritalStatus. r_c12_divorced.c12_divorced]]]]

	// if a person is married, in the next state, he can still be married:
	CTL_Formula[AG[implies_ctl[r_c6_maritalStatus.r_c8_married.c8_married,EX[r_c6_maritalStatus.r_c8_married.c8_married]]]]

	// if a person is neverMarried, in the next state he has to be either divorced or married:
	CTL_Formula[AG[implies_ctl[r_c6_maritalStatus.r_c8_married.c8_married,AX[or_ctl[r_c6_maritalStatus.r_c8_married.c8_married,r_c6_maritalStatus. r_c12_divorced.c12_divorced]]]]]

	// if a person is divorced, in the next state, he can get married:
	CTL_Formula[AG[implies_ctl[r_c6_maritalStatus. r_c12_divorced.c12_divorced,EX[r_c6_maritalStatus.r_c8_married.c8_married]]]]

	// if a person is divorced, in the next state, he can still be divorced:
	CTL_Formula[AG[implies_ctl[r_c6_maritalStatus. r_c12_divorced.c12_divorced,EX[r_c6_maritalStatus. r_c12_divorced.c12_divorced]]]]

	// if a person is divorced, in the next state he has to be either divorced or married:
	CTL_Formula[AG[implies_ctl[r_c6_maritalStatus. r_c12_divorced.c12_divorced,AX[or_ctl[r_c6_maritalStatus. r_c12_divorced.c12_divorced,r_c6_maritalStatus.r_c8_married.c8_married]]]]]

	// Bob will get married:
	CTL_Formula[EF[r_c6_maritalStatus.r_c8_married.c8_married]]
}



// NEW: an implicit state for the postcondition 'married'
sig c20_Bob_S1 in c1_Person {}
fact { c20_Bob_S1 = { p : c20_Bob | is_c1_Person_Married [p] } }
