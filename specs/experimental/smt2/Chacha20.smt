;(set-logic QF_ABV)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Chacha20: RFC 7539
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sort idx () (_ BitVec 4))
(define-sort uint32 () (_ BitVec 32))
(define-sort state () (Array idx uint32))
(define-sort key () (_ BitVec 256))
(define-sort nonce () (_ BitVec 96))
(define-sort counter () (_ BitVec 32))
(define-sort block () (_ BitVec 512))

(define-fun rol ((x uint32) (s uint32)) uint32
	    (bvor (bvshl x s) (bvlshr x (bvsub #x00000020 s))))

(define-fun line ((a idx) (b idx) (d idx) (s uint32) (m state)) state
 	    (let ((m1 (store m a (bvadd (select m a) (select m b)))))
	         (store m1 d (rol (bvxor (select m1 d) (select m1 a)) s))))

(define-fun quarter_round ((a idx) (b idx) (c idx) (d idx) (m state)) state
	    (let ((m1 (line a b d #x00000010 m)))
	    	 (let ((m2 (line c d b #x0000000c m1)))
		      (let ((m3 (line a b d #x00000008 m2)))
		           (line c d b #x00000007 m3)))))


(define-fun column_round ((m state)) state
	    (let ((m1 (quarter_round #x0 #x4 #x8 #xc m)))
	    	 (let ((m2 (quarter_round #x1 #x5 #x9 #xd m1)))
		      (let ((m3 (quarter_round #x2 #x6 #xa #xe m2)))
		           (quarter_round #x3 #x7 #xb #xf m3)))))


(define-fun diagonal_round ((m state)) state
	    (let ((m1 (quarter_round #x0 #x5 #xa #xf m)))
	    	 (let ((m2 (quarter_round #x1 #x6 #xb #xc m1)))
		      (let ((m3 (quarter_round #x2 #x7 #x8 #xd m2)))
		           (quarter_round #x3 #x4 #x9 #xe m3)))))


(define-fun double_round ((m state)) state  
	    (diagonal_round (column_round m)))

(define-fun rounds ((m state)) state  
	    (double_round 
	    (double_round 
	    (double_round 
	    (double_round 
	    (double_round 
	    (double_round 
	    (double_round 
	    (double_round 
	    (double_round 
	    (double_round m)))))))))))

(define-fun add_state ((m state) (s state)) state
	    (let ((s (store s #x0 (bvadd (select m #x0) (select s #x0)))))
	    (let ((s (store s #x1 (bvadd (select m #x1) (select s #x1)))))
	    (let ((s (store s #x2 (bvadd (select m #x2) (select s #x2)))))
	    (let ((s (store s #x3 (bvadd (select m #x3) (select s #x3)))))
	    (let ((s (store s #x4 (bvadd (select m #x4) (select s #x4)))))
	    (let ((s (store s #x5 (bvadd (select m #x5) (select s #x5)))))
	    (let ((s (store s #x6 (bvadd (select m #x6) (select s #x6)))))
	    (let ((s (store s #x7 (bvadd (select m #x7) (select s #x7)))))
	    (let ((s (store s #x8 (bvadd (select m #x8) (select s #x8)))))
	    (let ((s (store s #x9 (bvadd (select m #x9) (select s #x9)))))
	    (let ((s (store s #xa (bvadd (select m #xa) (select s #xa)))))
	    (let ((s (store s #xb (bvadd (select m #xb) (select s #xb)))))
	    (let ((s (store s #xc (bvadd (select m #xc) (select s #xc)))))
	    (let ((s (store s #xd (bvadd (select m #xd) (select s #xd)))))
	    (let ((s (store s #xe (bvadd (select m #xe) (select s #xe)))))
	    (let ((s (store s #xf (bvadd (select m #xf) (select s #xf)))))	
	         s)))))))))))))))))

(define-fun chacha20_core ((m state)) state  
	    (let ((s (rounds m)))
	         (add_state s m)))

(define-fun flip_endian ((x uint32)) uint32
	    (concat ((_ extract 7 0) x)
	    (concat ((_ extract 15 8) x)
	    (concat ((_ extract 23 16) x) ((_ extract 31 24) x)))))

(define-fun c0 () uint32 #x61707865)
(define-fun c1 () uint32 #x3320646e)
(define-fun c2 () uint32 #x79622d32)
(define-fun c3 () uint32 #x6b206574)

(declare-const sinit state)

(define-fun setup ((k key) (n nonce) (c counter)) state
            (let ((s1 (store sinit #x0 c0)))
            (let ((s2 (store s1 #x1 c1)))
            (let ((s3 (store s2 #x2 c2)))
            (let ((s4 (store s3 #x3 c3)))
            (let ((s5 (store s4 #x4 (flip_endian ((_ extract  255 224) k)))))
            (let ((s6 (store s5 #x5 (flip_endian ((_ extract  223 192) k)))))
            (let ((s7 (store s6 #x6 (flip_endian ((_ extract  191 160) k)))))
            (let ((s8 (store s7 #x7 (flip_endian ((_ extract  159 128) k)))))
            (let ((s9 (store s8 #x8 (flip_endian ((_ extract  127  96) k)))))
            (let ((s10 (store s9 #x9 (flip_endian ((_ extract  95 64) k)))))
            (let ((s11 (store s10 #xa (flip_endian ((_ extract  63 32) k)))))
            (let ((s12 (store s11 #xb (flip_endian ((_ extract  31 0) k)))))
            (let ((s13 (store s12 #xc c)))
            (let ((s14 (store s13 #xd (flip_endian ((_ extract 95 64) n)))))
            (let ((s15 (store s14 #xe (flip_endian ((_ extract 63 32) n)))))
            (let ((s16 (store s15 #xf (flip_endian ((_ extract 31 0) n)))))
	         s16)))))))))))))))))

(define-fun chacha20_block_state ((s0 state)) block
            (let ((st (chacha20_core s0)))
	         (concat (flip_endian (select st #x0))
	         (concat (flip_endian (select st #x1))
	         (concat (flip_endian (select st #x2))
	         (concat (flip_endian (select st #x3))
	         (concat (flip_endian (select st #x4))
	         (concat (flip_endian (select st #x5))
	         (concat (flip_endian (select st #x6))
	         (concat (flip_endian (select st #x7))
	         (concat (flip_endian (select st #x8))
	         (concat (flip_endian (select st #x9))
	         (concat (flip_endian (select st #xa))
	         (concat (flip_endian (select st #xb))
	         (concat (flip_endian (select st #xc))
	         (concat (flip_endian (select st #xd))
	         (concat (flip_endian (select st #xe)) 
		         (flip_endian (select st #xf)))))))))))))))))))
	  

(define-fun chacha20_block ((k key) (n nonce) (c counter)) block
	    (chacha20_block_state (setup k n c)))

;; Quarter Round RFC Test
(declare-const s state)
(assert (= (select s #x0) #x11111111))
(assert (= (select s #x1) #x01020304))
(assert (= (select s #x2) #x9b8d6f43))
(assert (= (select s #x3) #x01234567))
(assert (= (let ((x (quarter_round #x0 #x1 #x2 #x3 s))) (select x #x0)) #xea2a92f4))
(assert (= (let ((x (quarter_round #x0 #x1 #x2 #x3 s))) (select x #x1)) #xcb1cf8ce))
(assert (= (let ((x (quarter_round #x0 #x1 #x2 #x3 s))) (select x #x2)) #x4581472e))
(assert (= (let ((x (quarter_round #x0 #x1 #x2 #x3 s))) (select x #x3)) #x5881c4bb))
(echo "Running quarter_round RFC test:")
(check-sat)
;(get-model)

;; Chacha20 Block Function RFC Test Vector
(define-fun k () key #x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f)
(define-fun n () nonce #x000000090000004a00000000)
(define-fun c () counter #x00000001)
(define-fun s0 () state (setup k n c))

(assert (= (select s0 #x0) #x61707865))
(assert (= (select s0 #x1) #x3320646e))
(assert (= (select s0 #x2) #x79622d32))
(assert (= (select s0 #x3) #x6b206574))
(assert (= (select s0 #x4) #x03020100))
(assert (= (select s0 #x5) #x07060504))
(assert (= (select s0 #x6) #x0b0a0908))
(assert (= (select s0 #x7) #x0f0e0d0c))
(assert (= (select s0 #x8) #x13121110))
(assert (= (select s0 #x9) #x17161514))
(assert (= (select s0 #xa) #x1b1a1918))
(assert (= (select s0 #xb) #x1f1e1d1c))
(assert (= (select s0 #xc) #x00000001))
(assert (= (select s0 #xd) #x09000000))
(assert (= (select s0 #xe) #x4a000000))
(assert (= (select s0 #xf) #x00000000))
(echo "Running setup RFC test:")
(check-sat)
;(get-model)

(define-fun s20 () state (rounds s0))
(assert (= (select s20 #x0) #x837778ab))
(assert (= (select s20 #x1) #xe238d763))
(assert (= (select s20 #x2) #xa67ae21e))
(assert (= (select s20 #x3) #x5950bb2f))
(assert (= (select s20 #x4) #xc4f2d0c7))
(assert (= (select s20 #x5) #xfc62bb2f))
(assert (= (select s20 #x6) #x8fa018fc))
(assert (= (select s20 #x7) #x3f5ec7b7))
(assert (= (select s20 #x8) #x335271c2))
(assert (= (select s20 #x9) #xf29489f3))
(assert (= (select s20 #xa) #xeabda8fc))
(assert (= (select s20 #xb) #x82e46ebd))
(assert (= (select s20 #xc) #xd19c12b4))
(assert (= (select s20 #xd) #xb04e16de))
(assert (= (select s20 #xe) #x9e83d0cb))
(assert (= (select s20 #xf) #x4e3c50a2))
(echo "Running rounds RFC test:")
(check-sat)
;(get-model)

(define-fun key1 () block (chacha20_block k n c))
(assert (= key1 #x10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e))
(echo "Running chacha20_block RFC test:")
(check-sat)
;(get-model)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Vectorized Chacha20 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sort idx2 () (_ BitVec 2))
(define-sort uint32x4 () (Array idx2 uint32))
(define-sort state2 () (Array idx2 uint32x4))
(declare-const vinit uint32x4)

(define-fun rol2 ((v uint32x4) (s uint32)) uint32x4
	    (let ((v1 (store vinit #b00 (rol (select v #b00) s))))
	    (let ((v2 (store v1 #b01 (rol (select v #b01) s))))
	    (let ((v3 (store v2 #b10 (rol (select v #b10) s))))
	    (let ((v4 (store v3 #b11 (rol (select v #b11) s))))
	         v4)))))


(define-fun add2 ((x uint32x4) (y uint32x4)) uint32x4
	    (let ((v (store vinit #b00 (bvadd (select x #b00) (select y #b00)))))
	    (let ((v (store v #b01 (bvadd (select x #b01) (select y #b01)))))
	    (let ((v (store v #b10 (bvadd (select x #b10) (select y #b10)))))
	    (let ((v (store v #b11 (bvadd (select x #b11) (select y #b11)))))
	         v)))))

(define-fun xor2 ((x uint32x4) (y uint32x4)) uint32x4
	    (let ((v (store vinit #b00 (bvxor (select x #b00) (select y #b00)))))
	    (let ((v (store v #b01 (bvxor (select x #b01) (select y #b01)))))
	    (let ((v (store v #b10 (bvxor (select x #b10) (select y #b10)))))
	    (let ((v (store v #b11 (bvxor (select x #b11) (select y #b11)))))
	         v)))))


(define-fun line2 ((a idx2) (b idx2) (d idx2) (s uint32) (m state2)) state2
 	    (let ((m1 (store m a (add2 (select m a) (select m b)))))
	         (store m1 d (rol2 (xor2 (select m1 d) (select m1 a)) s))))


(define-fun shuffle_right ((x uint32x4) (n idx2)) uint32x4
	    (let ((v1 (store vinit #b00 (select x n))))
	    (let ((v2 (store v1 #b01 (select x (bvadd n #b01)))))
	    (let ((v3 (store v2 #b10 (select x (bvadd n #b10)))))
	    (let ((v4 (store v3 #b11 (select x (bvadd n #b11)))))
	         v4)))))

(define-fun shuffle0123 ((m state2)) state2
	    (let ((m1 (store m #b01 (shuffle_right (select m #b01) #b01))))
	    (let ((m2 (store m1 #b10 (shuffle_right (select m #b10) #b10))))
	    (let ((m3 (store m2 #b11 (shuffle_right (select m #b11) #b11))))
	         m3))))

(define-fun shuffle0321 ((m state2)) state2
	    (let ((m1 (store m #b01 (shuffle_right (select m #b01) #b11))))
	    (let ((m2 (store m1 #b10 (shuffle_right (select m #b10) #b10))))
	    (let ((m3 (store m2 #b11 (shuffle_right (select m #b11) #b01))))
	         m3))))
	    
(define-fun column_round2 ((m state2)) state2
	    (let ((m1 (line2 #b00 #b01 #b11 #x00000010 m)))
	    	 (let ((m2 (line2 #b10 #b11 #b01 #x0000000c m1)))
		      (let ((m3 (line2 #b00 #b01 #b11 #x00000008 m2)))
		           (line2 #b10 #b11 #b01 #x00000007 m3)))))


(define-fun diagonal_round2 ((m state2)) state2
	    (shuffle0321 (column_round2 (shuffle0123 m))))

(define-fun double_round2 ((m state2)) state2  
	    (diagonal_round2 (column_round2 m)))

(define-fun rounds2 ((m state2)) state2  
	    (double_round2 
	    (double_round2 
	    (double_round2 
	    (double_round2 
	    (double_round2 
	    (double_round2 
	    (double_round2 
	    (double_round2 
	    (double_round2 
	    (double_round2 m)))))))))))

(define-fun add_state2 ((x state2) (y state2)) state2
	    (let ((v0 (store x #b00 (add2 (select x #b00) (select y #b00)))))
	    (let ((v1 (store v0 #b01 (add2 (select x #b01) (select y #b01)))))
	    (let ((v2 (store v1 #b10 (add2 (select x #b10) (select y #b10)))))
	    (let ((v3 (store v2 #b11 (add2 (select x #b11) (select y #b11)))))
	         v3)))))

(define-fun chacha20_core2 ((m state2)) state2  
	    (add_state2 m (rounds2 m)))

(declare-const st0 state2)
(define-fun setup2 ((s0 state)) state2
	    (let ((v00 (store vinit  #b00 (select s0 #x0))))
	    (let ((v01 (store v00 #b01 (select s0 #x1))))
	    (let ((v02 (store v01 #b10 (select s0 #x2))))
	    (let ((v03 (store v02 #b11 (select s0 #x3))))
	    (let ((v10 (store vinit  #b00 (select s0 #x4))))
	    (let ((v11 (store v10 #b01 (select s0 #x5))))
	    (let ((v12 (store v11 #b10 (select s0 #x6))))
	    (let ((v13 (store v12 #b11 (select s0 #x7))))
	    (let ((v20 (store vinit  #b00 (select s0 #x8))))
	    (let ((v21 (store v20 #b01 (select s0 #x9))))
	    (let ((v22 (store v21 #b10 (select s0 #xa))))
	    (let ((v23 (store v22 #b11 (select s0 #xb))))
	    (let ((v30 (store vinit  #b00 (select s0 #xc))))
	    (let ((v31 (store v30 #b01 (select s0 #xd))))
	    (let ((v32 (store v31 #b10 (select s0 #xe))))
	    (let ((v33 (store v32 #b11 (select s0 #xf))))
	    (let ((st0 (store st0 #b00 v03))) 
	    (let ((st1 (store st0 #b01 v13))) 
	    (let ((st2 (store st1 #b10 v23))) 
	    (let ((st3 (store st2 #b11 v33)))
	         st3)))))))))))))))))))))
	    
	     
(define-fun chacha20_block2_state ((s0 state)) block
	    (let ((st (chacha20_core2 (setup2 s0))))
	         (concat (flip_endian (select (select st #b00) #b00))
	         (concat (flip_endian (select (select st #b00) #b01))
	         (concat (flip_endian (select (select st #b00) #b10))
	         (concat (flip_endian (select (select st #b00) #b11))
	         (concat (flip_endian (select (select st #b01) #b00))
	         (concat (flip_endian (select (select st #b01) #b01))
	         (concat (flip_endian (select (select st #b01) #b10))
	         (concat (flip_endian (select (select st #b01) #b11))
	         (concat (flip_endian (select (select st #b10) #b00))
	         (concat (flip_endian (select (select st #b10) #b01))
	         (concat (flip_endian (select (select st #b10) #b10))
	         (concat (flip_endian (select (select st #b10) #b11))
	         (concat (flip_endian (select (select st #b11) #b00))
	         (concat (flip_endian (select (select st #b11) #b01))
	         (concat (flip_endian (select (select st #b11) #b10))
	                 (flip_endian (select (select st #b11) #b11)))))))))))))))))))


(define-fun chacha20_block2 ((k key) (n nonce) (c counter)) block
	         (chacha20_block2_state (setup k n c)))

;; Chacha20 Block Function RFC Test Vector
(define-fun key2 () block (chacha20_block2 k n c))
(assert (= key2 #x10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e))
(echo "Running vectorized chacha20_block2 RFC test:")
(check-sat)
;(get-model)


(assert (forall ((m state))
        (= (chacha20_block_state m) (chacha20_block2_state m))))

(echo "Verifying chacha20_block_state = chacha_block2_state:")
(check-sat)
;(get-model)


