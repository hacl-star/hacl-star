module Device

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST
open LowStar.BufferOps

#set-options "--z3rlimit 25 --fuel 1 --ifuel 1 --__no_positivity"

(*** Linked lists *)
noeq
type ll_ (a: Type0) =
  B.pointer_or_null (cell a)

and cell (a: Type0) = {
  next: ll_ a;
  data: a;
}

noeq
type ll (a: Type0) = {
  l: ll_ a;
  elems: Ghost.erased (list a); // Ghost representation of the list
  r : HS.rid; (* For footprint reasoning *)
}

/// Well-formedness
///
/// Pointers are live and [l] can be represented by [elems].
let rec ll_wf (#a : Type0) (h : HS.mem) (l : ll_ a) (elems : list a) :
  GTot Type (decreases elems) =
  B.live h l /\ (
  match Ghost.reveal elems with
  | [] ->
    B.g_is_null l
  | x :: elems' ->
    B.length l == 1 /\ (
    let { data=data; next=next } = B.get h l 0 in
    x == data /\
    ll_wf h next (G.hide elems')
  ))

let ll_inv (#a : Type0) (h: HS.mem) (l : ll a) : GTot Type =
  ll_wf h l.l l.elems

val footprint_: (#a: Type0) -> (h: HS.mem) -> (l: ll_ a) -> (n: list a) -> Ghost B.loc
  (requires (ll_wf h l n))
  (ensures (fun refs -> True))
  (decreases n)

let rec footprint_ #a h l n =
  if B.g_is_null l
  then B.loc_none
  else
    let {next = next} = B.get h l 0 in
    let refs = footprint_ h next (G.hide (L.tl n)) in
    B.loc_union (B.loc_addr_of_buffer l) refs

val footprint : (#a: Type0) -> (h: HS.mem) -> (l: ll a) -> Ghost B.loc
  (requires (ll_inv h l))
  (ensures (fun refs -> True))

let footprint #a h l = footprint_ h l.l l.elems

/// Framing lemmas
let rec frame_ (#a: Type0) (l: ll_ a) (n: list a) (r: B.loc) (h0 h1: HS.mem): Lemma
  (requires (
    ll_wf h0 l n /\
    B.loc_disjoint r (footprint_ h0 l n) /\
    B.modifies r h0 h1
  ))
  (ensures (
    ll_wf h1 l n /\
    footprint_ h1 l n == footprint_ h0 l n /\
    ll_wf h1 l n
  ))
  (decreases n)
  [ SMTPat (ll_wf h1 l n); SMTPat (B.modifies r h0 h1) ]
=
  if B.g_is_null l then
    ()
  else
    frame_ (B.deref h0 l).next (L.tl n) r h0 h1

let frame (#a: Type0) (l: ll a) (r: B.loc) (h0 h1: HS.mem): Lemma
  (requires (
    ll_inv h0 l /\
    B.loc_disjoint r (footprint h0 l) /\
    B.modifies r h0 h1
  ))
  (ensures (
    ll_inv h1 l /\
    footprint h1 l == footprint h0 l /\
    ll_inv h1 l
  ))
  [ SMTPat (ll_inv h1 l); SMTPat (B.modifies r h0 h1) ]
=
  frame_ l.l l.elems r h0 h1

let rec inv_loc_in_footprint_ (#a: Type0) (h:HS.mem) (l: ll_ a) (n: list a) :
  Lemma
    (requires (ll_wf h l n))
    (ensures (B.loc_in (footprint_ h l n) h))
    (decreases n) 
    [ SMTPat (ll_wf h l n) ] =
  if B.g_is_null l then
    ()
  else
    inv_loc_in_footprint_ h (B.deref h l).next (L.tl n)

let inv_loc_in_footprint (#a: Type0) (h:HS.mem) (l: ll a) :
  Lemma
    (requires (ll_inv h l))
    (ensures (B.loc_in (footprint h l) h))
    [ SMTPat (ll_inv h l) ] =
  inv_loc_in_footprint_ h l.l l.elems

(*** Map *)

inline_for_extraction noextract
let find_t (k a : Type) : Type =
  k ->
  l:ll (k * a) ->
  Stack (option a)
    (requires (fun h0 -> ll_inv h0 l))
    (ensures (fun h0 _ h1 -> True))

inline_for_extraction noextract
noeq type map (a : Type) = {
  k : Type;
  find : find_t k a;
}

inline_for_extraction noextract
noeq type eq_index = {
  k: Type0;
  t: Type0
} 

/// Auxiliary definitions
inline_for_extraction
let alloc #a (init : a) :
  ST.StackInline (B.buffer a)
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 ->
    B.live h1 b /\
    B.alloc_post_mem_common b h0 h1 (Seq.create 1 init) /\
    B.length b = 1 /\
    B.frameOf b = HS.get_tip h0 /\
    B.frameOf b <> HyperStack.root    
  )) =
  B.alloca init 1ul

inline_for_extraction
let upd
  (#a:Type0) (#rrel #rel:B.srel a)
  (b:B.mbuffer a rrel rel)
  (v:a) :
  Stack unit
    (requires (fun h -> B.live h b /\ 0 < B.length b /\
                      rel (B.as_seq h b) (Seq.upd (B.as_seq h b) 0 v)))
    (ensures (fun h _ h' -> (not (B.g_is_null b)) /\
                          B.modifies (B.loc_buffer b) h h' /\
                          B.live h' b /\
                          B.as_seq h' b == Seq.upd (B.as_seq h b) 0 v))
  = B.upd b 0ul v

[@Meta.Attribute.specialize]
assume val eq: #i:eq_index -> i.k -> i.k -> bool

(** Auxiliary definition for [find] *)
inline_for_extraction noextract
[@Meta.Attribute.specialize]
let find (#i : eq_index) (x : i.k) (ls : ll (i.k * i.t)) :
  Stack (option i.t)
  (requires (fun h0 -> ll_inv h0 ls))
  (ensures (fun h0 _ h1 -> True))
  =
  (* Push a new frame for stack allocation *)
  push_frame ();
  (* Stack allocation *)
  let lsp = alloc ls.l in
  (* This pointer is ghost, and will disappear at extraction: we need it
     to track the pure view of the list *)
  let glsp = alloc ls.elems in
  let b = alloc true in
  let inv h =
    let l = B.deref h lsp in
    let elems = G.reveal (B.deref h glsp) in
    ll_wf h l elems /\
    B.live h lsp /\
    B.live h glsp /\
    B.live h b /\
    B.loc_disjoint (footprint_ h l elems) (B.loc_buffer lsp) /\
    B.loc_disjoint (footprint_ h l elems) (B.loc_buffer glsp) /\
    B.loc_disjoint (footprint_ h l elems) (B.loc_buffer b) /\
    True
  in
  let test_pre h0 =
    inv h0
  in
  let test_post x h1 =
    inv h1 /\
    x = B.deref h1 b
  in
  [@inline_let]
  let test () : Stack bool (requires test_pre) (ensures (fun h0 b h1 -> test_post b h1)) =
    !* b
  in
  [@inline_let]
  let body () : Stack unit
    (requires (fun h0 -> test_post true h0))
    (ensures (fun h0 _ h1 -> test_pre h1)) =
    (**) let h0 = ST.get () in
    let ls = !* lsp in
    (* Check if we reached the end of the list *)
    if B.is_null ls then
      begin
      (* End of the list: exit *)
      upd b false
      end
    else
      begin
      (* Get the current element and the tail *)
      let { data=data; next=tl } = !* ls in
      let (x', _) = data in
      (* Check the key *)
      if eq x x' then
        (* Found: exit the loop *)
        upd b false
      else
        begin
        (* Not found: update the pointers and continue *)
        let els = !* glsp in
        (**) begin
        (**) let etl = (Cons?.tl els) in
        (**) assert (ll_wf h0 ls els);
        (**) assert (ll_wf h0 tl etl)
        (**) end;
        B.upd lsp 0ul tl;
        (**) let h1 = ST.get () in
        B.upd glsp 0ul (Cons?.tl els); (* This is ghost *)
        (**) let hf = ST.get () in
        (**) begin
        (**) let h = hf in
        (**) let l = B.deref h lsp in
        (**) let elems = G.reveal (B.deref h glsp) in
        (**) assert (B.loc_includes (footprint_ h0 l elems) (footprint_ hf l elems))
        (**) end
        end
      end
  in
  C.Loops.while #test_pre #test_post test body;
  (* Retrieve the found element, if there is *)
  let ls = !* lsp in
  let o: option i.t =
    if B.is_null ls then
      None
    else
      begin
      let { data=data; next=tl } = !* ls in
      let (_, y) = data in
      Some y
      end
  in
  (* Pop the frame (invalidates the stack allocated pointers) *)
  pop_frame ();
  (* Return *)
  o

#set-options "--print_implicits --print_effect_args"

let device_find_higher_t: #i: Device.eq_index -> p: Type0 -> Prims.Tot Type0 = fun #i p ->
  x: Mkeq_index?.k i -> ls: Device.ll (Mkeq_index?.k i * Mkeq_index?.t i)
    -> FStar.HyperStack.ST.Stack (FStar.Pervasives.Native.option (Mkeq_index?.t i))
        (fun h0 -> Prims.l_and p (Device.ll_inv #(Mkeq_index?.k i * Mkeq_index?.t i) h0 ls))
        (fun _ _ _ -> Prims.l_True)

let device_find_higher:

    #i: Device.eq_index ->
    p: Type0 ->
    arg_Device_eq:
      (fun #i _ -> _: Mkeq_index?.k i -> _: Mkeq_index?.k i -> Prims.Tot Prims.bool) #i p
  -> Prims.Tot (Device.device_find_higher_t #i p)
=
fun #i _ arg_Device_eq x ls ->
  (let _ = FStar.HyperStack.ST.push_frame () in
    let lsp =
      Device.alloc #(Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i)))
        (Mkll?.l #(Mkeq_index?.k i (Mkeq_index?.t i)) ls)
    in
    let glsp =
      Device.alloc #(FStar.Ghost.erased (Prims.list (Mkeq_index?.k i (Mkeq_index?.t i))))
        (Mkll?.elems #(Mkeq_index?.k i (Mkeq_index?.t i)) ls)
    in
    let b = Device.alloc #Prims.bool true in
    let inv h =
      let l =
        LowStar.Monotonic.Buffer.deref #(Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i)))
          #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i))))
          #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i))))
          h
          lsp
      in
      let elems =
        FStar.Ghost.reveal #(Prims.list (Mkeq_index?.k i (Mkeq_index?.t i)))
          (LowStar.Monotonic.Buffer.deref #(FStar.Ghost.erased (Prims.list (Mkeq_index?.k i
                          (Mkeq_index?.t i))))
              #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k i
                              (Mkeq_index?.t i)))))
              #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k i
                              (Mkeq_index?.t i)))))
              h
              glsp)
      in
      Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Prims.l_and (Device.ll_wf
                                    #(Mkeq_index?.k i (Mkeq_index?.t i))
                                    h
                                    l
                                    elems)
                                (LowStar.Monotonic.Buffer.live #(Device.ll_ (Mkeq_index?.k i
                                            (Mkeq_index?.t i)))
                                    #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i
                                                (Mkeq_index?.t i))))
                                    #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i
                                                (Mkeq_index?.t i))))
                                    h
                                    lsp))
                            (LowStar.Monotonic.Buffer.live #(FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                            i
                                            (Mkeq_index?.t i))))
                                #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                                i
                                                (Mkeq_index?.t i)))))
                                #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                                i
                                                (Mkeq_index?.t i)))))
                                h
                                glsp))
                        (LowStar.Monotonic.Buffer.live #Prims.bool
                            #(LowStar.Buffer.trivial_preorder Prims.bool)
                            #(LowStar.Buffer.trivial_preorder Prims.bool)
                            h
                            b))
                    (LowStar.Monotonic.Buffer.loc_disjoint (Device.footprint_ #(Mkeq_index?.k i
                                (Mkeq_index?.t i))
                            h
                            l
                            elems)
                        (LowStar.Monotonic.Buffer.loc_buffer #(Device.ll_ (Mkeq_index?.k i
                                    (Mkeq_index?.t i)))
                            #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i
                                        (Mkeq_index?.t i))))
                            #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i
                                        (Mkeq_index?.t i))))
                            lsp)))
                (LowStar.Monotonic.Buffer.loc_disjoint (Device.footprint_ #(Mkeq_index?.k i
                            (Mkeq_index?.t i))
                        h
                        l
                        elems)
                    (LowStar.Monotonic.Buffer.loc_buffer #(FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                    i
                                    (Mkeq_index?.t i))))
                        #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                        i
                                        (Mkeq_index?.t i)))))
                        #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                        i
                                        (Mkeq_index?.t i)))))
                        glsp)))
            (LowStar.Monotonic.Buffer.loc_disjoint (Device.footprint_ #(Mkeq_index?.k i
                        (Mkeq_index?.t i))
                    h
                    l
                    elems)
                (LowStar.Monotonic.Buffer.loc_buffer #Prims.bool
                    #(LowStar.Buffer.trivial_preorder Prims.bool)
                    #(LowStar.Buffer.trivial_preorder Prims.bool)
                    b)))
        Prims.l_True
    in
    let test_pre h0 = inv h0 in
    let test_post x h1 =
      Prims.l_and (inv h1)
        (Prims.b2t (Prims.op_Equality #Prims.bool
                x
                (LowStar.Monotonic.Buffer.deref #Prims.bool
                    #(LowStar.Buffer.trivial_preorder Prims.bool)
                    #(LowStar.Buffer.trivial_preorder Prims.bool)
                    h1
                    b)))
    in
    [@@ FStar.Pervasives.inline_let ]let test _ =
      !*Prims.bool #(LowStar.Buffer.trivial_preorder Prims.bool)
        #(LowStar.Buffer.trivial_preorder Prims.bool)
        b
      <:
      FStar.HyperStack.ST.Stack Prims.bool test_pre (fun _ b h1 -> test_post b h1)
    in
    [@@ FStar.Pervasives.inline_let ]let body _ =
      (let h0 = FStar.HyperStack.ST.get () in
        let ls =
          !*(Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i))) #(LowStar.Buffer.trivial_preorder (Device.ll_
                    (Mkeq_index?.k i (Mkeq_index?.t i))))
            #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i))))
            lsp
        in
        let _ =
          LowStar.Monotonic.Buffer.is_null #(Device.cell (Mkeq_index?.k i (Mkeq_index?.t i)))
            #(LowStar.Buffer.trivial_preorder (Device.cell (Mkeq_index?.k i (Mkeq_index?.t i))))
            #(LowStar.Buffer.trivial_preorder (Device.cell (Mkeq_index?.k i (Mkeq_index?.t i))))
            ls
          <:
          Prims.bool
        in
        (if _
          then
            Device.upd #Prims.bool
              #(LowStar.Buffer.trivial_preorder Prims.bool)
              #(LowStar.Buffer.trivial_preorder Prims.bool)
              b
              false
          else
            let _ =
              !*(Device.cell (Mkeq_index?.k i (Mkeq_index?.t i))) #(LowStar.Buffer.trivial_preorder (
                      Device.cell (Mkeq_index?.k i (Mkeq_index?.t i))))
                #(LowStar.Buffer.trivial_preorder (Device.cell (Mkeq_index?.k i (Mkeq_index?.t i))))
                ls
            in
            (let { next = tl ; data = data } = _ in
              let _ = data in
              (let FStar.Pervasives.Native.Mktuple2 #_ #_ x' _ = _ in
                (if arg_Device_eq x x'
                  then
                    Device.upd #Prims.bool
                      #(LowStar.Buffer.trivial_preorder Prims.bool)
                      #(LowStar.Buffer.trivial_preorder Prims.bool)
                      b
                      false
                  else
                    let els =
                      !*(FStar.Ghost.erased (Prims.list (Mkeq_index?.k i (Mkeq_index?.t i)))) #(LowStar.Buffer.trivial_preorder
                            (FStar.Ghost.erased (Prims.list (Mkeq_index?.k i (Mkeq_index?.t i)))))
                        #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                        i
                                        (Mkeq_index?.t i)))))
                        glsp
                    in
                    [@@ FStar.Pervasives.inline_let ]let _ =
                      let etl =
                        Cons?.tl #(Mkeq_index?.k i (Mkeq_index?.t i))
                          (FStar.Ghost.reveal #(Prims.list (Mkeq_index?.k i (Mkeq_index?.t i))) els)
                      in
                      [@@ FStar.Pervasives.inline_let ]let _ =
                        assert (Device.ll_wf #(Mkeq_index?.k i (Mkeq_index?.t i))
                              h0
                              ls
                              (FStar.Ghost.reveal #(Prims.list (Mkeq_index?.k i (Mkeq_index?.t i)))
                                  els))
                      in
                      assert (Device.ll_wf #(Mkeq_index?.k i (Mkeq_index?.t i)) h0 tl etl)
                    in
                    let _ =
                      LowStar.Monotonic.Buffer.upd #(Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i)))
                        #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i
                                    (Mkeq_index?.t i))))
                        #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i
                                    (Mkeq_index?.t i))))
                        lsp
                        0ul
                        tl
                    in
                    let h1 = FStar.HyperStack.ST.get () in
                    let _ =
                      LowStar.Monotonic.Buffer.upd #(FStar.Ghost.erased (Prims.list (Mkeq_index?.k i
                                    (Mkeq_index?.t i))))
                        #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                        i
                                        (Mkeq_index?.t i)))))
                        #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                        i
                                        (Mkeq_index?.t i)))))
                        glsp
                        0ul
                        (FStar.Ghost.hide #(Prims.list (Mkeq_index?.k i (Mkeq_index?.t i)))
                            (Cons?.tl #(Mkeq_index?.k i (Mkeq_index?.t i))
                                (FStar.Ghost.reveal #(Prims.list (Mkeq_index?.k i (Mkeq_index?.t i))
                                    )
                                    els)))
                    in
                    let hf = FStar.HyperStack.ST.get () in
                    let h = hf in
                    let l =
                      LowStar.Monotonic.Buffer.deref #(Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i)
                            ))
                        #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i
                                    (Mkeq_index?.t i))))
                        #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i
                                    (Mkeq_index?.t i))))
                        h
                        lsp
                    in
                    let elems =
                      FStar.Ghost.reveal #(Prims.list (Mkeq_index?.k i (Mkeq_index?.t i)))
                        (LowStar.Monotonic.Buffer.deref #(FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                        i
                                        (Mkeq_index?.t i))))
                            #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                            i
                                            (Mkeq_index?.t i)))))
                            #(LowStar.Buffer.trivial_preorder (FStar.Ghost.erased (Prims.list (Mkeq_index?.k
                                            i
                                            (Mkeq_index?.t i)))))
                            h
                            glsp)
                    in
                    assert (LowStar.Monotonic.Buffer.loc_includes (Device.footprint_ #(Mkeq_index?.k
                                  i
                                  (Mkeq_index?.t i))
                              h0
                              l
                              elems)
                          (Device.footprint_ #(Mkeq_index?.k i (Mkeq_index?.t i)) hf l elems)))
                <:
                Prims.unit)
              <:
              Prims.unit)
            <:
            Prims.unit)
        <:
        Prims.unit)
      <:
      FStar.HyperStack.ST.Stack Prims.unit (fun h0 -> test_post true h0) (fun _ _ h1 -> test_pre h1)
    in
    let _ = C.Loops.while #test_pre #test_post test body in
    let ls =
      !*(Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i))) #(LowStar.Buffer.trivial_preorder (Device.ll_
                (Mkeq_index?.k i (Mkeq_index?.t i))))
        #(LowStar.Buffer.trivial_preorder (Device.ll_ (Mkeq_index?.k i (Mkeq_index?.t i))))
        lsp
    in
    let o =
      let _ =
        LowStar.Monotonic.Buffer.is_null #(Device.cell (Mkeq_index?.k i (Mkeq_index?.t i)))
          #(LowStar.Buffer.trivial_preorder (Device.cell (Mkeq_index?.k i (Mkeq_index?.t i))))
          #(LowStar.Buffer.trivial_preorder (Device.cell (Mkeq_index?.k i (Mkeq_index?.t i))))
          ls
        <:
        Prims.bool
      in
      (if _
        then FStar.Pervasives.Native.None #(Mkeq_index?.t i)
        else
          let _ =
            !*(Device.cell (Mkeq_index?.k i (Mkeq_index?.t i))) #(LowStar.Buffer.trivial_preorder (Device.cell
                      (Mkeq_index?.k i (Mkeq_index?.t i))))
              #(LowStar.Buffer.trivial_preorder (Device.cell (Mkeq_index?.k i (Mkeq_index?.t i))))
              ls
          in
          (let { next = _ ; data = data } = _ in
            let _ = data in
            (let FStar.Pervasives.Native.Mktuple2 #_ #_ _ y = _ in
              FStar.Pervasives.Native.Some #(Mkeq_index?.t i) y)
            <:
            FStar.Pervasives.Native.option (Mkeq_index?.t i))
          <:
          FStar.Pervasives.Native.option (Mkeq_index?.t i))
      <:
      FStar.Pervasives.Native.option (Mkeq_index?.t i)
    in
    let _ = FStar.HyperStack.ST.pop_frame () in
    o)
  <:
  FStar.HyperStack.ST.Stack (FStar.Pervasives.Native.option (Mkeq_index?.t i))
    (fun h0 -> Device.ll_inv #(Mkeq_index?.k i * Mkeq_index?.t i) h0 ls)
    (fun _ _ _ -> Prims.l_True)

%splice [ ] (Meta.Interface.specialize (`eq_index) [
  `find
])

(*** Map Instantiation *)
inline_for_extraction noextract
let string_eq_type = {
  t = string;
  eq = (fun x y -> x = y); // In the paper: String.eq
}

let find_s = (mk_map string_eq_type int).find

(*** Device *)
type bytes = Seq.seq FStar.UInt8.t
type ckey = Seq.seq FStar.UInt8.t

inline_for_extraction noextract
type send_t (pid : Type0) =
  pid ->
  dv:ll (pid * ckey) ->
  bytes ->
  Stack (option bytes)
    (requires (fun h0 -> ll_inv h0 dv))
    (ensures (fun _ _ _ -> True))

inline_for_extraction noextract
type recv_t (pid : Type0) =
  pid ->
  dv:ll (pid * ckey) ->
  bytes ->
  Stack (option bytes)
    (requires (fun h0 -> ll_inv h0 dv))
    (ensures (fun _ _ _ -> True))

inline_for_extraction noextract
noeq type device = {
  pid : Type;
  send : send_t pid;
  recv : recv_t pid;
}

noeq type cipher = {
  enc : ckey -> bytes -> bytes;
  dec : ckey -> bytes -> option bytes;
}

let mk_device (m : map ckey) (c : cipher) :
  d:device{d.pid == m.k} = {
  pid = m.k;
  send = (fun pid dv plain ->
    match m.find pid dv with
    | None -> None
    | Some sk -> Some (c.enc sk plain));
  recv = (fun pid dv secret ->
    match m.find pid dv with
    | None -> None
    | Some sk -> c.dec sk secret)
}
