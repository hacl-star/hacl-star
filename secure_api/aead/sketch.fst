module Connection

val global_region : rid
val doom_region : rid{disjoint global_region doom_region}

type id = x:(AEAD.id * AEAD.id){fst x <> snd x}

let peer_id (x:id) = snd x, fst x

type conn (i:id) =
  | MkConn: r:rid
          -> w:rid
          -> reader:aead_state (fst i) Reader{log_region reader = r}
          -> writer:aead_state (snd i) Writer{log_region writer = w}
          -> conn i

let footprint #i (c:conn i) : set (rid * option (set addr))
  let MkConn _ _ _ writer = c in
  AEAD.footprint writer //log_region + global

let peers #i #j (c:conn i) (d:conn j) =
  peer_id i = j /\
  AEAD.peers (MkConn?.reader c) (MkConn?.writer c) /\ //implies that they share the same log
  AEAD.peers (MkConn?.writer c) (MkConn?.reader c)

let conn_inv #i (c:conn i) h =
  let MkConn _ _ reader writer = c in
  AEADInv reader h /\
  AEADInv writer h

let my_nonce   (i:id) : nonce = let _reader_id, writer_id = i in AEAD.nonce writer_id
let peers_nonce (i:id) : nonce = let reader_id, _writer_id = i in AEAD.nonce reader_id

////////////////////////////////////////////////////////////////////////////////

val nonce_to_region: MonotoneMap.id global_region nonce (fun _ -> rid) (fun table -> ...)

val conn_table: MonotoneMap.t global_region id conn (fun (table:DM.t id conn) ->
    (forall i j. if peer_id i = j then peers table.[i] table.[j]
            else footprint table.[i] `disjoint` footprint table.[j])

let global_inv (h:heap) =
  (forall i. conn_inv (h.[conn_table].[i]) h) /\
  (forall i. let c = h.[conn_table].[i] in
        let writer_region = MkConn?.w c in
        safeId i ==> h.[nonce_to_region].[my_nonce c] = writer_region)


let gen (i:id) (writer_region:rid) :
  ST (conn i)
     (requires (fun h -> safeId i ==> Some writer_region == nonce_to_region.[my_nonce i] /\
                      global_inv h0))
     (ensures (fun h0 c h1 -> modifies global_region h0 h1 /\
                           MkConn?.w = writer_region /\
                           global_inv h1 /\
                           conn_inv c h))
  = match !conn_table.[i] with
    | None -> //need to create both sides and put them in the table
      let my_writer, their_reader =
        AEAD.gen (snd i) writer_region in
      let their_region =
        match !nonce_to_region.[peers_nonce i] with
        | Some r -> r
        | None -> //this is a bad connection; it's doomed
          doom_region in
      let their_writer, my_reader =
        AEAD.gen (fst i) thei_region in
      let c = (MkConn their_region writer_region my_reader my_writer) in
      insert conn_table i c
      insert conn_table (peer_id i) (MkConn writer_region their_region their_reader their_writer);
      c
    | Some c -> c
