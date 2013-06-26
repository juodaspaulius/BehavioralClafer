/*
All clafers: 9 | Abstract: 3 | Concrete: 6 | References: 0
Constraints: 4
Goals: 0
Global scope: 1..*
All names unique: False
*/
open util/integer
pred show {}
run  show for 1 but 0 c12_divorced, 1 c1_Person, 1 c2_age, 1 c6_maritalStatus, 0 c7_neverMarried, 0 c8_married

abstract sig c1_Person
{ r_c2_age : one c2_age
, r_c6_maritalStatus : one c6_maritalStatus }
{ (this.@r_c2_age.@ref) >= 0 }

sig c2_age
{ ref : one Int }
{ one @r_c2_age.this }

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

abstract sig c13_NewBorn extends c1_Person
{}
{ ((this.@r_c2_age.@ref) = 0) && (some (this.@r_c6_maritalStatus).@r_c7_neverMarried) }

abstract sig c20_IllegallyMarried extends c1_Person
{}
{ ((this.@r_c2_age.@ref) = 1) && (some (this.@r_c6_maritalStatus).@r_c8_married) }

one sig c27_Bob extends c1_Person
{}

