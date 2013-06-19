/*
All clafers: 6 | Abstract: 1 | Concrete: 3 | References: 2
Constraints: 3
Goals: 0
Global scope: 1..*
All names unique: False
*/
open util/integer
pred show {}
run show for 1 but 2 c19_parents, 3 c1_Person, 2 c3_kids

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
, r_c29_behave_well : lone c29_behave_well }
{ 2 <= #r_c19_parents and #r_c19_parents <= 2
  all disj x, y : this.@r_c19_parents | (x.@ref) != (y.@ref) }

sig c19_parents
{ ref : one c2_Parent }
{ one @r_c19_parents.this }

sig c29_behave_well
{}
{ one @r_c29_behave_well.this }

