/*
All clafers: 24 | Abstract: 6 | Concrete: 11 | References: 7
Constraints: 20
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
, r_c19_M : c19_M -> Time
, r_c29_Rec : one c29_Rec }
{ all t : Time | one r_c9_PStatus.t && lone r_c19_M.t
  all t : (Time <: first)  | all disj x, y : this.@r_c9_PStatus.t | (x.@ref) != (y.@ref)
  all t : (Time <: first)  | all disj x, y : this.@r_c19_M.t | (x.@ref) != (y.@ref)
  all disj x, y : this.@r_c29_Rec | (x.@ref) != (y.@ref)
  all t : (Time <: first)  | (this.(@r_c9_PStatus.t.@ref)) = c5_Dropped
  all t : (Time <: first)  | (some t':t.*(Time <: next + loop) | (this.(@r_c9_PStatus.t'.@ref)) = c7_Delivered)
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | ((this.(@r_c9_PStatus.t'.@ref)) = c7_Delivered) => ((some loop and all t'':t'.*(Time <: next + loop) | (this.(@r_c9_PStatus.t''.@ref)) = c7_Delivered)))
  all t : (Time <: first)  | ((some t':t.*(Time <: next + loop) | (this.(@r_c9_PStatus.t'.@ref)) = c7_Delivered)) => ((some t':t.*(Time <: next + loop) | ((this.(@r_c9_PStatus.t'.@ref)) = c5_Dropped) || ((this.(@r_c9_PStatus.t'.@ref)) = c7_Delivered) and ( all t'':t.*(Time <: next + loop) & ^(Time <: next + loop).t'|!((this.(@r_c9_PStatus.t''.@ref)) = c6_InTransit))))
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | ((this.(@r_c9_PStatus.t'.@ref)) = c6_InTransit) => ((let t''=t'.(Time <: next + loop) | some t'' and !((this.(@r_c9_PStatus.t''.@ref)) = c5_Dropped))))
  all t : (Time <: first)  | ((some loop and all t':t.*(Time <: next + loop) | !((this.(@r_c9_PStatus.t'.@ref)) = c7_Delivered))) || ((some t':t.*(Time <: next + loop) | (this.(@r_c9_PStatus.t'.@ref)) = c6_InTransit and ( all t'':t.*(Time <: next + loop) & ^(Time <: next + loop).t'|!((this.(@r_c9_PStatus.t''.@ref)) = c7_Delivered))))
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | (((this.(@r_c9_PStatus.t'.@ref)) = c6_InTransit) && ((let t''=t'.(Time <: next + loop) | some t'' and (this.(@r_c9_PStatus.t''.@ref)) = c7_Delivered))) => (some this.@r_c19_M.t'))
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | (some this.@r_c19_M.t') => ((this.(@r_c9_PStatus.t'.@ref)) != c5_Dropped)) }

sig c9_PStatus
{ ref : one c4_ParcelStatus }
{ one @r_c9_PStatus.Time.this }

sig c19_M
{ ref : one c136_Messenger }
{ one @r_c19_M.Time.this }

sig c29_Rec
{ ref : one c115_Recipient }
{ one @r_c29_Rec.this }

abstract sig c115_Recipient
{ r_c116_RLoc : c116_RLoc -> Time
, r_c126_Addr : one c126_Addr }
{ all t : Time | one r_c116_RLoc.t
  all t : (Time <: first)  | all disj x, y : this.@r_c116_RLoc.t | (x.@ref) != (y.@ref)
  all disj x, y : this.@r_c126_Addr | (x.@ref) != (y.@ref) }

sig c116_RLoc
{ ref : one c1_RecipientLocation }
{ one @r_c116_RLoc.Time.this }

sig c126_Addr
{ ref : one c216_Address }
{ one @r_c126_Addr.this }

abstract sig c136_Messenger
{ r_c137_P : c137_P -> Time
, r_c147_Location : c147_Location -> Time }
{ all t : Time | lone r_c137_P.t && one r_c147_Location.t
  all t : (Time <: first)  | all disj x, y : this.@r_c137_P.t | (x.@ref) != (y.@ref)
  all t : (Time <: first)  | all disj x, y : this.@r_c147_Location.t | (x.@ref) != (y.@ref)
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | (some this.@r_c137_P.t') => ((((((this.@r_c137_P.t').(@ref.(@r_c9_PStatus.t'.@ref))) = c6_InTransit) && ((this.(@r_c147_Location.t'.@ref)) = (((this.@r_c137_P.t').(@ref.@r_c29_Rec)).(@ref.(@r_c126_Addr.@ref))))) && ((((this.@r_c137_P.t').(@ref.@r_c29_Rec)).(@ref.(@r_c116_RLoc.t'.@ref))) = c2_AtHome)) <=> ((((this.@r_c137_P.t').(@ref.(@r_c9_PStatus.t'.@ref))) = c6_InTransit) && ((let t''=t'.(Time <: next + loop) | some t'' and ((this.@r_c137_P.t'').(@ref.(@r_c9_PStatus.t''.@ref))) = c7_Delivered)))))
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | (some this.@r_c137_P.t') => (((this.@r_c137_P.t').(@ref.(@r_c19_M.t'.@ref))) = this))
  all t : (Time <: first)  | (some loop and all t':t.*(Time <: next + loop) | (some this.@r_c137_P.t') => ((some t'':t'.*(Time <: next + loop) | ((this.@r_c137_P.t'').(@ref.(@r_c9_PStatus.t''.@ref))) = c7_Delivered and ( all t''':t'.*(Time <: next + loop) & ^(Time <: next + loop).t''|some this.@r_c137_P.t''')))) }

sig c137_P
{ ref : one c8_Parcel }
{ one @r_c137_P.Time.this }

sig c147_Location
{ ref : one c216_Address }
{ one @r_c147_Location.Time.this }

abstract sig c216_Address
{}

one sig c217_AlloyBook extends c8_Parcel
{}
{ (this.(@r_c29_Rec.@ref)) = c222_Bob }

one sig c221_Mark extends c136_Messenger
{}

one sig c222_Bob extends c115_Recipient
{}
{ (this.(@r_c126_Addr.@ref)) = c226_Main1 }

one sig c226_Main1 extends c216_Address
{}

one sig c227_Main2 extends c216_Address
{}

one sig c228_Main3 extends c216_Address
{}

