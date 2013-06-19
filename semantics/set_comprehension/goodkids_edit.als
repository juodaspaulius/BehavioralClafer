/*
All clafers: 6 | Abstract: 1 | Concrete: 3 | References: 2
Constraints: 3
Goals: 0
Global scope: 1..*
All names unique: False
*/
open util/integer
open util/ordering[Time]
pred show {}
run show for 10


sig Time {loop: lone Time}

fact Loop {loop in last->Time}

abstract sig c1_Person
{}

sig c2_Parent extends c1_Person
{ r_c3_kids : some c3_kids }
{ all disj x, y : this.@r_c3_kids | (x.@ref) != (y.@ref)
  this in ((this.@r_c3_kids).(@ref.(@r_c19_parents.@ref))) }

sig c3_kids
{ ref : one c18_Kid }
{ one @r_c3_kids.this }

sig c18_Kid extends c1_Person
{ r_c19_parents : set c19_parents
, r_c29_behave_well : c29_behave_well->Time }
{ 
  all t: Time | lone r_c29_behave_well.t
  2 <= #r_c19_parents and #r_c19_parents <= 2
  all disj x, y : this.@r_c19_parents | (x.@ref) != (y.@ref) }

sig c19_parents
{ ref : one c2_Parent }
{ one @r_c19_parents.this }

sig c29_behave_well
{}
{ one @r_c29_behave_well.Time.this }

// goodkids = { let k: Kid | k.behave_well && X k.behave_well }
fun goodKids : c18_Kid{
  {k: c18_Kid | all t: first | some k.r_c29_behave_well.t 
	 and some t.(next + loop) and 
    	let t'=t.(next+loop) | some k.r_c29_behave_well.t' 
	}
}

// # goodkids = 2
fact {
	# goodKids = 4
}

