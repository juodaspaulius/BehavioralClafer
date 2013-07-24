/*
All clafers: 21 | Abstract: 6 | Concrete: 9 | References: 6
Constraints: 13
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

abstract sig c1_RecipientLocation
{}

one sig c2_AtHome extends c1_RecipientLocation
{}

one sig c3_Away extends c1_RecipientLocation
{}

abstract sig c4_ParcelStatus
{}

one sig c5_Dropped extends c4_ParcelStatus
{}

one sig c6_InTransit extends c4_ParcelStatus
{}

one sig c7_Delivered extends c4_ParcelStatus
{}

abstract sig c8_Parcel
{ r_c9_PStatus : c9_PStatus -> Time
, r_c19_Rec : c19_Rec -> Time }
{ all t : Time | one r_c9_PStatus.t && one r_c19_Rec.t
  all t : (Time <: first)  | all disj x, y : this.@r_c9_PStatus.t | (x.@ref) != (y.@ref)
  all t : (Time <: first)  | all disj x, y : this.@r_c19_Rec.t | (x.@ref) != (y.@ref)
  all t : (Time <: first)  | (this.(@r_c9_PStatus.t.@ref)) = c6_InTransit
  all t : (Time <: first)  | (some t':t.*(Time <: next + loop) | (this.(@r_c9_PStatus.t'.@ref)) = c7_Delivered)
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | ((this.(@r_c9_PStatus.t'.@ref)) = c7_Delivered) => ((some loop and all t'':t'.*(Time <: next + loop) | (this.(@r_c9_PStatus.t''.@ref)) = c7_Delivered))) }

sig c9_PStatus
{ ref : one c4_ParcelStatus }
{ one @r_c9_PStatus.Time.this }

sig c19_Rec
{ ref : one c45_Recipient }
{ one @r_c19_Rec.Time.this }

abstract sig c45_Recipient
{ r_c46_RLoc : c46_RLoc -> Time
, r_c56_Addr : one c56_Addr }
{ all t : Time | one r_c46_RLoc.t
  all t : (Time <: first)  | all disj x, y : this.@r_c46_RLoc.t | (x.@ref) != (y.@ref)
  all disj x, y : this.@r_c56_Addr | (x.@ref) != (y.@ref) }

sig c46_RLoc
{ ref : one c1_RecipientLocation }
{ one @r_c46_RLoc.Time.this }

sig c56_Addr
{ ref : one c134_Address }
{ one @r_c56_Addr.this }

abstract sig c66_Messenger
{ r_c67_P : c67_P -> Time
, r_c77_Location : c77_Location -> Time }
{ all t : Time | one r_c67_P.t && one r_c77_Location.t
  all t : (Time <: first)  | all disj x, y : this.@r_c67_P.t | (x.@ref) != (y.@ref)
  all t : (Time <: first)  | all disj x, y : this.@r_c77_Location.t | (x.@ref) != (y.@ref)
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | (((this.@r_c67_P.t').(@ref.(@r_c9_PStatus.t'.@ref))) = c6_InTransit) || (((this.@r_c67_P.t').(@ref.(@r_c9_PStatus.t'.@ref))) = c7_Delivered))
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | (((((this.@r_c67_P.t').(@ref.(@r_c9_PStatus.t'.@ref))) = c6_InTransit) && ((this.(@r_c77_Location.t'.@ref)) = (((this.@r_c67_P.t').(@ref.@r_c19_Rec.t')).(@ref.(@r_c56_Addr.@ref))))) && ((((this.@r_c67_P.t').(@ref.@r_c19_Rec.t')).(@ref.(@r_c46_RLoc.t'.@ref))) = c2_AtHome)) <=> ((((this.@r_c67_P.t').(@ref.(@r_c9_PStatus.t'.@ref))) = c6_InTransit) && ((let t''=t'.(Time <: next + loop) | some t'' and ((this.@r_c67_P.t'').(@ref.(@r_c9_PStatus.t''.@ref))) = c7_Delivered)))) }

sig c67_P
{ ref : one c8_Parcel }
{ one @r_c67_P.Time.this }

sig c77_Location
{ ref : one c134_Address }
{ one @r_c77_Location.Time.this }

abstract sig c134_Address
{}

one sig c135_AlloyBook extends c8_Parcel
{}
{ all t : (Time <: first)  | (this.(@r_c19_Rec.t.@ref)) = c140_Bob }

one sig c139_Mark extends c66_Messenger
{}

one sig c140_Bob extends c45_Recipient
{}
{ (this.(@r_c56_Addr.@ref)) = c144_Main1 }

one sig c144_Main1 extends c134_Address
{}

