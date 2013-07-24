/*
All clafers: 14 | Abstract: 1 | Concrete: 13 | References: 0
Constraints: 4
Goals: 0
Global scope: 1..*
All names unique: False
*/
open util/integer
open util/ordering[Time]
pred show {}
-- run show for 1 but 2 c12_maritalStatus, 2 c1_Person, 2 c2_firstName, 2 c3_lastName, 2 c4_gender, 2 c7_age
run show for 8

sig Time {loop: lone Time}
fact Loop {loop in last->Time}

abstract sig c1_Person
{ r_c2_firstName : one c2_firstName
, r_c3_lastName : one c3_lastName
, r_c4_gender : one c4_gender
, r_c7_age : c7_age -> Time
, r_c8_alive : c8_alive -> Time
, r_c12_maritalStatus : one c12_maritalStatus}
{ (this.(@r_c7_age.Time.@ref)) >= 0 

  // Adding constraints that enforce regular implicit cardinality constraints
  all t: Time | one r_c7_age.t
  all t: Time | lone r_c8_alive.t

	// age only increases
	// G( let x = age | X age >= x)
	all t: Time <: first | (some loop and all t': t.*(Time <: next + loop) | let x = this.@r_c7_age.t.@ref | // G and bind x to age ref
		some t'.(Time <: next + loop) and let t'' = t'.(Time <: next + loop) |  this.@r_c7_age.t''.@ref >= x)  // <- X age >= x
}

sig c2_firstName
{ ref : one Int }
{ one @r_c2_firstName.this }

sig c3_lastName
{ ref : one Int }
{ one @r_c3_lastName.this }

sig c4_gender
{ r_c5_male : lone c5_male
, r_c6_female : lone c6_female }
{ one @r_c4_gender.this
  let children = (r_c5_male + r_c6_female) | one children }

sig c5_male
{}
{ one @r_c5_male.this }

sig c6_female
{}
{ one @r_c6_female.this }

sig c7_age
{ ref : one Int }
{ one @r_c7_age.Time.this }

sig c8_alive
{}
{ one @r_c8_alive.Time.this }

sig c12_maritalStatus
{ r_c13_neverMarried : c13_neverMarried -> Time
, r_c14_married : c14_married -> Time
, r_c18_divorced : c18_divorced -> Time}
{
all t:Time | lone r_c13_neverMarried.t
all t:Time | lone r_c14_married.t
all t:Time | lone r_c18_divorced.t
// one @r_c12_maritalStatus.this
all t: Time | let children = (r_c13_neverMarried + r_c14_married + r_c18_divorced).t | one children

// neverMarried precedes divorced
//	!divorced W neverMarried = G !divorced or (!divorced U neverMarried)
	all t: Time <: first | (some loop and all t': t.*(Time <: next + loop) | no this.@r_c18_divorced.t' // <- G !divorced
	 or some t' : t.*(Time <: next+loop) | no this.@r_c18_divorced.t' and all t'' : t.*(next + loop) & ^(Time <: next+loop).t' |  some this.@r_c13_neverMarried.t'' ) // <- (!divorced U neverMarried)

// married precedes divorced
//	!divorced W married = G !divorced or (!divorced U married)
	all t: Time <: first | (some loop and all t': t.*(Time <: next + loop) | no this.@r_c18_divorced.t' // <- G !divorced
	 or some t' : t.*(Time <: next+loop) | no this.@r_c18_divorced.t' and all t'' : t.*(next + loop) & ^(Time <: next+loop).t' |  some this.@r_c14_married.t'') // <- (!divorced U married)

// divorced to married
//	divorced W married = G divorced or (divorced U married)
	all t: Time <: first | (some loop and all t': t.*(Time <: next + loop) | some this.@r_c18_divorced.t' // <- G divorced 
 	 or  some t' : t.*(Time <: next+loop) | some this.@r_c18_divorced.t' and all t'' : t.*(next + loop) & ^(Time <: next+loop).t' |  some this.@r_c14_married.t'') // <- (divorced U married)

// from married or divorced you can't go to neverMarried
//  [G (divorced || married => G !neverMarried) ]
	all t: Time <: first | (some loop and all t': t.*(Time <: next + loop) | // G
		(some this.@r_c18_divorced.t' or some this.@r_c14_married.t') implies // <-divorced  or married implies
			(some loop and all t'': t'.*(Time <: next + loop) | // another G
				no this.@r_c13_neverMarried.t''))

// from neverMarried you cannot go to divorced
//    [ G(neverMarried => X !divorced ) ]
	all t: Time <: first | (some loop and all t': t.*(Time <: next + loop) | // G
		some this.@r_c13_neverMarried.t' implies // <- neverMarried implies
			some t'.(Time <: next + loop) and let t'' = t'.(Time <: next + loop) | no this.@r_c18_divorced.t'' ) // <- X !divorced
}

sig c13_neverMarried
{}
{ one @r_c13_neverMarried.Time.this }

sig c14_married
{}
{ one @r_c14_married.Time.this
  all t: Time | ((((this.~(@r_c14_married.t)).~(@r_c12_maritalStatus)).(@r_c7_age.t.@ref)) >= 18) }

sig c18_divorced
{}
{ one @r_c18_divorced.Time.this }

one sig c19_Tom extends c1_Person
{}
{ (((this.(@r_c2_firstName.@ref)) = 0) && ((this.(@r_c3_lastName.@ref)) = 1)) && (some (this.@r_c4_gender).@r_c5_male) }

one sig c30_Alice extends c1_Person
{}
{ ((((this.(@r_c2_firstName.@ref)) = 2) && ((this.(@r_c3_lastName.@ref)) = 3)) && (some (this.@r_c4_gender).@r_c6_female)) && ((this.(@r_c7_age.first.@ref)) = 25) }

fact {

}


