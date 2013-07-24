/*
All clafers: 23 | Abstract: 6 | Concrete: 11 | References: 6
Constraints: 12
Goals: 0
Global scope: 1..*
All names unique: False
*/
open util/integer
pred show {}
run  show for 1 but 3 c105_Address, 1 c106_AlloyBook, 1 c110_Mark, 1 c114_Bob, 1 c118_Main1, 1 c119_Main2, 1 c120_Main3, 1 c18_Rec, 2 c1_RecipientStatus, 1 c2_AtHome, 1 c31_Recipient, 1 c32_RStatus, 1 c3_Away, 1 c42_Addr, 2 c4_ParcelStatus, 1 c52_Messenger, 1 c53_P, 1 c5_InTransit, 1 c63_Location, 1 c6_Delivered, 1 c7_Parcel, 1 c8_PStatus

abstract sig c1_RecipientStatus
{}

one sig c2_AtHome extends c1_RecipientStatus
{}

one sig c3_Away extends c1_RecipientStatus
{}

abstract sig c4_ParcelStatus
{}

one sig c5_InTransit extends c4_ParcelStatus
{}

one sig c6_Delivered extends c4_ParcelStatus
{}

abstract sig c7_Parcel
{ r_c8_PStatus : one c8_PStatus
, r_c18_Rec : one c18_Rec }
{ all disj x, y : this.@r_c8_PStatus | (x.@ref) != (y.@ref)
  all disj x, y : this.@r_c18_Rec | (x.@ref) != (y.@ref)
  (this.(@r_c8_PStatus.@ref)) = c5_InTransit }

sig c8_PStatus
{ ref : one c4_ParcelStatus }
{ one @r_c8_PStatus.this }

sig c18_Rec
{ ref : one c31_Recipient }
{ one @r_c18_Rec.this }

abstract sig c31_Recipient
{ r_c32_RStatus : one c32_RStatus
, r_c42_Addr : one c42_Addr }
{ all disj x, y : this.@r_c32_RStatus | (x.@ref) != (y.@ref)
  all disj x, y : this.@r_c42_Addr | (x.@ref) != (y.@ref) }

sig c32_RStatus
{ ref : one c1_RecipientStatus }
{ one @r_c32_RStatus.this }

sig c42_Addr
{ ref : one c105_Address }
{ one @r_c42_Addr.this }

abstract sig c52_Messenger
{ r_c53_P : one c53_P
, r_c63_Location : one c63_Location
, r_c73_Delivering : lone c73_Delivering }
{ all disj x, y : this.@r_c53_P | (x.@ref) != (y.@ref)
  all disj x, y : this.@r_c63_Location | (x.@ref) != (y.@ref)
  ((((this.@r_c53_P).(@ref.(@r_c8_PStatus.@ref))) = c5_InTransit) && ((this.(@r_c63_Location.@ref)) = (((this.@r_c53_P).(@ref.@r_c18_Rec)).(@ref.(@r_c42_Addr.@ref))))) <=> (some this.@r_c73_Delivering)
  ((some (this.@r_c53_P).(@ref.@r_c8_PStatus)) && ((this.(@r_c63_Location.@ref)) = (((this.@r_c53_P).(@ref.@r_c18_Rec)).(@ref.(@r_c42_Addr.@ref))))) <=> (some this.@r_c73_Delivering) }

sig c53_P
{ ref : one c7_Parcel }
{ one @r_c53_P.this }

sig c63_Location
{ ref : one c105_Address }
{ one @r_c63_Location.this }

sig c73_Delivering
{}
{ one @r_c73_Delivering.this }

abstract sig c105_Address
{}

one sig c106_AlloyBook extends c7_Parcel
{}
{ (this.(@r_c18_Rec.@ref)) = c114_Bob }

one sig c110_Mark extends c52_Messenger
{}
{ (this.(@r_c53_P.@ref)) = c106_AlloyBook }

one sig c114_Bob extends c31_Recipient
{}
{ (this.(@r_c42_Addr.@ref)) = c118_Main1 }

one sig c118_Main1 extends c105_Address
{}

one sig c119_Main2 extends c105_Address
{}

one sig c120_Main3 extends c105_Address
{}

