module F = Format;;
module XO = XmlOutput;;

type t = Integers | Rationals | Algebraic;;

let xml_of_domain dom = match dom with
  | Integers -> "<naturals/>"
  | Rationals -> "<rationals><delta><rational><numerator>1</numerator><denominator>64</denominator></rational></delta></rationals>"
  | Algebraic -> "<algebraicNumbers><delta><rational><numerator>1</numerator><denominator>64</denominator></rational></delta></algebraicNumbers>"
;;

let xml_of_domain' dom = XO.node "domain" [match dom with
  | Integers -> XO.node "naturals" []
  | Rationals -> XO.node "rationals" [XO.node "delta" [
    XO.node "rational" [
      XO.int "numerator" 1;
      XO.int "denominator" 64
    ]]]
  | Algebraic -> XO.node "algebraicNumbers" [XO.node "delta" [
    XO.node "rational" [
      XO.int "numerator" 1;
      XO.int "denominator" 64
    ]]]]

let domain_of_rat_real rat real =  
  if real then Algebraic 
  else if rat <> 1 then Rationals  
  else Integers;;

let fprintfx_domain fmt dom dim = 
 let bdom = xml_of_domain dom in
 if dim = 1 then F.fprintf fmt "@{<domain>%s@}" bdom else
 F.fprintf fmt 
  "@{<domain>@{<matrices>@{<dimension>%d@}@{<strictDimension>1@}@{<domain>%s@}@}@}"
  dim bdom
;;

let fprintfx_domain' dom dim =
  let bdom = xml_of_domain' dom in
  if dim = 1
    then bdom
    else XO.node "domain" [XO.node "matrices" [
      XO.int "dimension" dim;
      XO.int "strictDimension" 1;
      bdom
    ]]
;;
