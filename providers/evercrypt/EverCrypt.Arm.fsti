module EverCrypt.Arm

open FStar.HyperStack.ST

val has_neon: bool

val check_neon: unit -> Stack bool
  (requires fun _ ->
    EverCrypt.TargetConfig.(aarch32 || aarch64))
  (ensures fun h0 b h1 ->
    h0 == h1 /\ (
    b ==> has_neon))
