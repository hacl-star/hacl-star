module EverCrypt.Curve25519

module B = LowStar.Buffer

[@ CInline ]
let has_adx_bmi2 (): Stack bool
  (fun _ -> True)
  (ensures (fun h0 b h1 ->
    B.(modifies B.loc_none h0 h1) /\
    (b ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled))))
=
  let has_bmi2 = EverCrypt.AutoConfig2.has_bmi2 () in
  let has_adx = EverCrypt.AutoConfig2.has_adx () in
  has_bmi2 && has_adx

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let secret_to_public pub priv =
  if EverCrypt.TargetConfig.hacl_can_compile_vale then
    let has_bmi2 = EverCrypt.AutoConfig2.has_bmi2 () in
    let has_adx = EverCrypt.AutoConfig2.has_adx () in
    if (has_bmi2 && has_adx) then
      Hacl.Curve25519_64.secret_to_public pub priv
    else
      Hacl.Curve25519_51.secret_to_public pub priv
  else
    Hacl.Curve25519_51.secret_to_public pub priv

let scalarmult shared my_priv their_pub =
  if EverCrypt.TargetConfig.hacl_can_compile_vale then
    let has_bmi2 = EverCrypt.AutoConfig2.has_bmi2 () in
    let has_adx = EverCrypt.AutoConfig2.has_adx () in
    if (has_bmi2 && has_adx) then
      Hacl.Curve25519_64.scalarmult shared my_priv their_pub
    else
      Hacl.Curve25519_51.scalarmult shared my_priv their_pub
  else
    Hacl.Curve25519_51.scalarmult shared my_priv their_pub

let ecdh shared my_priv their_pub =
  if EverCrypt.TargetConfig.hacl_can_compile_vale then
    let has_bmi2 = EverCrypt.AutoConfig2.has_bmi2 () in
    let has_adx = EverCrypt.AutoConfig2.has_adx () in
    if (has_bmi2 && has_adx) then
      Hacl.Curve25519_64.ecdh shared my_priv their_pub
    else
      Hacl.Curve25519_51.ecdh shared my_priv their_pub
  else
    Hacl.Curve25519_51.ecdh shared my_priv their_pub
