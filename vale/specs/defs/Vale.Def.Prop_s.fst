module Vale.Def.Prop_s
open FStar.Mul

// Prims.logical (which is private to Prims) and prop0 are synonyms for Type0 in F*,
// but are not synonyms in Vale's type system:
// - importFStarTypes.exe interprets Prims.logical and prop0 as "prop"
// - importFStarTypes.exe interprets Type0 as "Type(0)"
// In Vale's type system, "prop" is a type, while "Type(0)" is a kind, not a type.
let prop0 = Type0
