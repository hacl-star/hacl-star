;(set-logic QF_ABV)
(set-option :produce-models true)

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
(get-model)

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
(get-model)

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
(get-model)

(define-fun key1 () block (chacha20_block k n c))
(assert (= key1 #x10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e))
(echo "Running chacha20_block RFC test:")
(check-sat)
(get-model)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Vectorized Chacha20 (128-bit)
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
	    
	     
(define-fun uint32x4_serialize ((x uint32x4)) (_ BitVec 128)
	    (concat (flip_endian (select x #b00))
	    (concat (flip_endian (select x #b01))
	    (concat (flip_endian (select x #b10))
	    	    (flip_endian (select x #b11))))))

(define-fun chacha20_block2_state ((s0 state)) block
	    (let ((st (chacha20_core2 (setup2 s0))))
	         (concat (uint32x4_serialize (select st #b00))
	         (concat (uint32x4_serialize (select st #b01))
	         (concat (uint32x4_serialize (select st #b10))
	         	 (uint32x4_serialize (select st #b11)))))))

(define-fun chacha20_block2 ((k key) (n nonce) (c counter)) block
	         (chacha20_block2_state (setup k n c)))

;; Chacha20 Block Function RFC Test Vector
(define-fun key2 () block (chacha20_block2 k n c))
;(assert (= key2 #x10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e))
(echo "Running vectorized chacha20_block2 RFC test:")
(check-sat)
(get-model)


(assert (forall ((m state))
        (= (chacha20_block_state m) (chacha20_block2_state m))))
(echo "Verifying chacha20_block_state = chacha_block2_state:")
(check-sat)
(get-model)

(assert (forall ((k key) (n nonce) (c counter))
        (= (chacha20_block k n c) (chacha20_block2 k n c))))
(echo "Verifying chacha20_block = chacha_block2:")
(check-sat)
(get-model)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Vectorized Chacha20 (256-bit)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sort idx3 () (_ BitVec 3))
(define-sort uint32x8 () (Array idx3 uint32))
(define-sort state3 () (Array idx uint32x8))
(declare-const v32x8 uint32x8)
(define-sort block8 () (_ BitVec 4096))

(define-fun rol3 ((v uint32x8) (s uint32)) uint32x8
	    (let ((v (store v #b000 (rol (select v #b000) s))))
	    (let ((v (store v #b001 (rol (select v #b001) s))))
	    (let ((v (store v #b010 (rol (select v #b010) s))))
	    (let ((v (store v #b011 (rol (select v #b011) s))))
	    (let ((v (store v #b100 (rol (select v #b100) s))))
	    (let ((v (store v #b101 (rol (select v #b101) s))))
	    (let ((v (store v #b110 (rol (select v #b110) s))))
	    (let ((v (store v #b111 (rol (select v #b111) s))))
	         v)))))))))


(define-fun add3 ((x uint32x8) (y uint32x8)) uint32x8
	    (let ((v (store v32x8 #b000 (bvadd (select x #b000) (select y #b000)))))
	    (let ((v (store v #b001 (bvadd (select x #b001) (select y #b001)))))
	    (let ((v (store v #b010 (bvadd (select x #b010) (select y #b010)))))
	    (let ((v (store v #b011 (bvadd (select x #b011) (select y #b011)))))
	    (let ((v (store v #b100 (bvadd (select x #b100) (select y #b100)))))
	    (let ((v (store v #b101 (bvadd (select x #b101) (select y #b101)))))
	    (let ((v (store v #b110 (bvadd (select x #b110) (select y #b110)))))
	    (let ((v (store v #b111 (bvadd (select x #b111) (select y #b111)))))
	         v)))))))))

(define-fun xor3 ((x uint32x8) (y uint32x8)) uint32x8
	    (let ((v (store v32x8 #b000 (bvxor (select x #b000) (select y #b000)))))
	    (let ((v (store v #b001 (bvxor (select x #b001) (select y #b001)))))
	    (let ((v (store v #b010 (bvxor (select x #b010) (select y #b010)))))
	    (let ((v (store v #b011 (bvxor (select x #b011) (select y #b011)))))
	    (let ((v (store v #b100 (bvxor (select x #b100) (select y #b100)))))
	    (let ((v (store v #b101 (bvxor (select x #b101) (select y #b101)))))
	    (let ((v (store v #b110 (bvxor (select x #b110) (select y #b110)))))
	    (let ((v (store v #b111 (bvxor (select x #b111) (select y #b111)))))
	         v)))))))))

(define-fun line3 ((a idx) (b idx) (d idx) (s uint32) (m state3)) state3
 	    (let ((m1 (store m a (add3 (select m a) (select m b)))))
	         (store m1 d (rol3 (xor3 (select m1 d) (select m1 a)) s))))


(define-fun column_round3 ((m state3)) state3
	    (let ((m (line3 #x0 #x4 #xc #x00000010 m)))
       	    (let ((m (line3 #x1 #x5 #xd #x00000010 m)))
	    (let ((m (line3 #x2 #x6 #xe #x00000010 m)))
       	    (let ((m (line3 #x3 #x7 #xf #x00000010 m)))

	    (let ((m (line3 #x8 #xc #x4 #x0000000c m)))
       	    (let ((m (line3 #x9 #xd #x5 #x0000000c m)))
	    (let ((m (line3 #xa #xe #x6 #x0000000c m)))
       	    (let ((m (line3 #xb #xf #x7 #x0000000c m)))

	    (let ((m (line3 #x0 #x4 #xc #x00000008 m)))
       	    (let ((m (line3 #x1 #x5 #xd #x00000008 m)))
	    (let ((m (line3 #x2 #x6 #xe #x00000008 m)))
       	    (let ((m (line3 #x3 #x7 #xf #x00000008 m)))

	    (let ((m (line3 #x8 #xc #x4 #x00000007 m)))
       	    (let ((m (line3 #x9 #xd #x5 #x00000007 m)))
	    (let ((m (line3 #xa #xe #x6 #x00000007 m)))
       	    (let ((m (line3 #xb #xf #x7 #x00000007 m)))
	         m)))))))))))))))))

(define-fun diagonal_round3 ((m state3)) state3
	    (let ((m (line3 #x0 #x5 #xf #x00000010 m)))
       	    (let ((m (line3 #x1 #x6 #xc #x00000010 m)))
	    (let ((m (line3 #x2 #x7 #xd #x00000010 m)))
       	    (let ((m (line3 #x3 #x4 #xe #x00000010 m)))

	    (let ((m (line3 #xa #xf #x5 #x0000000c m)))
       	    (let ((m (line3 #xb #xc #x6 #x0000000c m)))
	    (let ((m (line3 #x8 #xd #x7 #x0000000c m)))
       	    (let ((m (line3 #x9 #xe #x4 #x0000000c m)))

	    (let ((m (line3 #x0 #x5 #xf #x00000008 m)))
       	    (let ((m (line3 #x1 #x6 #xc #x00000008 m)))
	    (let ((m (line3 #x2 #x7 #xd #x00000008 m)))
       	    (let ((m (line3 #x3 #x4 #xe #x00000008 m)))

	    (let ((m (line3 #xa #xf #x5 #x00000007 m)))
       	    (let ((m (line3 #xb #xc #x6 #x00000007 m)))
	    (let ((m (line3 #x8 #xd #x7 #x00000007 m)))
       	    (let ((m (line3 #x9 #xe #x4 #x00000007 m)))
	         m)))))))))))))))))


(define-fun double_round3 ((m state3)) state3  
	    (diagonal_round3 (column_round3 m)))

(define-fun rounds3 ((m state3)) state3  
	    (double_round3 
	    (double_round3 
	    (double_round3 
	    (double_round3 
	    (double_round3 
	    (double_round3 
	    (double_round3 
	    (double_round3 
	    (double_round3 
	    (double_round3 m)))))))))))

(define-fun add_state3 ((x state3) (y state3)) state3
	    (let ((x (store x #x0 (add3 (select x #x0) (select y #x0)))))
	    (let ((x (store x #x1 (add3 (select x #x1) (select y #x1)))))
	    (let ((x (store x #x2 (add3 (select x #x2) (select y #x2)))))
	    (let ((x (store x #x3 (add3 (select x #x3) (select y #x3)))))
	    (let ((x (store x #x4 (add3 (select x #x4) (select y #x4)))))
	    (let ((x (store x #x5 (add3 (select x #x5) (select y #x5)))))
	    (let ((x (store x #x6 (add3 (select x #x6) (select y #x6)))))
	    (let ((x (store x #x7 (add3 (select x #x7) (select y #x7)))))
	    (let ((x (store x #x8 (add3 (select x #x8) (select y #x8)))))
	    (let ((x (store x #x9 (add3 (select x #x9) (select y #x9)))))
	    (let ((x (store x #xa (add3 (select x #xa) (select y #xa)))))
	    (let ((x (store x #xb (add3 (select x #xb) (select y #xb)))))
	    (let ((x (store x #xc (add3 (select x #xc) (select y #xc)))))
	    (let ((x (store x #xd (add3 (select x #xd) (select y #xd)))))
	    (let ((x (store x #xe (add3 (select x #xe) (select y #xe)))))
	    (let ((x (store x #xf (add3 (select x #xf) (select y #xf)))))
	    	 x)))))))))))))))))

(define-fun chacha20_core3 ((m state3)) state3  
	    (add_state3 m (rounds3 m)))

(declare-const stinit3 state3)

(define-fun load32x8 ((x uint32)) uint32x8
	     (let ((v (store v32x8 #b000 x)))
	     (let ((v (store v #b001 x)))
	     (let ((v (store v #b010 x)))
	     (let ((v (store v #b011 x)))
	     (let ((v (store v #b100 x)))
	     (let ((v (store v #b101 x)))
	     (let ((v (store v #b110 x)))
	     (let ((v (store v #b111 x)))
	          v)))))))))

(define-fun load_counter ((c uint32)) uint32x8
	     (let ((v (store v32x8 #b000 c)))
	     (let ((v (store v #b001 (bvadd c #x00000001))))
	     (let ((v (store v #b010 (bvadd c #x00000010))))
	     (let ((v (store v #b011 (bvadd c #x00000011))))
	     (let ((v (store v #b100 (bvadd c #x00000100))))
	     (let ((v (store v #b101 (bvadd c #x00000101))))
	     (let ((v (store v #b110 (bvadd c #x00000110))))
	     (let ((v (store v #b111 (bvadd c #x00000111))))
	          v)))))))))

(define-fun setup3 ((s0 state)) state3
	    (let ((v0 (load32x8 (select s0 #x0))))
	    (let ((v1 (load32x8 (select s0 #x1))))
	    (let ((v2 (load32x8 (select s0 #x2))))
	    (let ((v3 (load32x8 (select s0 #x3))))
	    (let ((v4 (load32x8 (select s0 #x4))))
	    (let ((v5 (load32x8 (select s0 #x5))))
	    (let ((v6 (load32x8 (select s0 #x6))))
	    (let ((v7 (load32x8 (select s0 #x7))))
	    (let ((v8 (load32x8 (select s0 #x8))))
	    (let ((v9 (load32x8 (select s0 #x9))))
	    (let ((v10 (load32x8 (select s0 #xa))))
	    (let ((v11 (load32x8 (select s0 #xb))))
	    (let ((v12 (load_counter (select s0 #xc))))
	    (let ((v13 (load32x8 (select s0 #xd))))
	    (let ((v14 (load32x8 (select s0 #xe))))
	    (let ((v15 (load32x8 (select s0 #xf))))

	    (let ((st (store stinit3 #x0 v0))) 
	    (let ((st (store st #x1 v1)))
	    (let ((st (store st #x2 v2)))
	    (let ((st (store st #x3 v3)))
	    (let ((st (store st #x4 v4)))
	    (let ((st (store st #x5 v5)))
	    (let ((st (store st #x6 v6)))
	    (let ((st (store st #x7 v7)))
	    (let ((st (store st #x8 v8)))
	    (let ((st (store st #x9 v9)))
	    (let ((st (store st #xa v10)))
	    (let ((st (store st #xb v11)))
	    (let ((st (store st #xc v12)))
	    (let ((st (store st #xd v13)))
	    (let ((st (store st #xe v14)))
	    (let ((st (store st #xf v15)))
	         st)))))))))))))))))))))))))))))))))
	    
	     
(define-fun uint32x8_serialize ((x uint32x8)) (_ BitVec 256)
	    (concat (flip_endian (select x #b000))
	    (concat (flip_endian (select x #b001))
	    (concat (flip_endian (select x #b010))
	    (concat (flip_endian (select x #b011))
	    (concat (flip_endian (select x #b100))
	    (concat (flip_endian (select x #b101))
	    (concat (flip_endian (select x #b110))
	            (flip_endian (select x #b111))))))))))

(define-fun column_top ((m state3) (i idx3)) uint32x8
            (let ((v (store v32x8 #b000 (select (select m #x0) i))))
            (let ((v (store v #b001 (select (select m #x1) i))))
            (let ((v (store v #b010 (select (select m #x2) i))))
            (let ((v (store v #b011 (select (select m #x3) i))))
            (let ((v (store v #b100 (select (select m #x4) i))))
            (let ((v (store v #b101 (select (select m #x5) i))))
            (let ((v (store v #b110 (select (select m #x6) i))))
            (let ((v (store v #b111 (select (select m #x7) i))))
	         v)))))))))


(define-fun column_bottom ((m state3) (i idx3)) uint32x8
            (let ((v (store v32x8 #b000 (select (select m #x8) i))))
            (let ((v (store v #b001 (select (select m #x9) i))))
            (let ((v (store v #b010 (select (select m #xa) i))))
            (let ((v (store v #b011 (select (select m #xb) i))))
            (let ((v (store v #b100 (select (select m #xc) i))))
            (let ((v (store v #b101 (select (select m #xd) i))))
            (let ((v (store v #b110 (select (select m #xe) i))))
            (let ((v (store v #b111 (select (select m #xf) i))))
	         v)))))))))

(define-fun transpose16x8 ((m state3)) state3
	    (let ((r (store m #x0 (column_top m #b000))))
	    (let ((r (store r #x1 (column_bottom m #b000))))
	    (let ((r (store r #x2 (column_top m #b001))))
	    (let ((r (store r #x3 (column_bottom m #b001))))
	    (let ((r (store r #x4 (column_top m #b010))))
	    (let ((r (store r #x5 (column_bottom m #b010))))
	    (let ((r (store r #x6 (column_top m #b011))))
	    (let ((r (store r #x7 (column_bottom m #b011))))
	    (let ((r (store r #x8 (column_top m #b100))))
	    (let ((r (store r #x9 (column_bottom m #b100))))
	    (let ((r (store r #xa (column_top m #b101))))
	    (let ((r (store r #xb (column_bottom m #b101))))
	    (let ((r (store r #xc (column_top m #b110))))
	    (let ((r (store r #xd (column_bottom m #b110))))
	    (let ((r (store r #xe (column_top m #b111))))
	    (let ((r (store r #xf (column_bottom m #b111))))
	         r)))))))))))))))))
	    

(define-fun chacha20_block3_state ((s0 state)) block8
	    (let ((st (chacha20_core3 (setup3 s0))))
	    (let ((st (transpose16x8 st)))
	         (concat (uint32x8_serialize (select st #x0))
	         (concat (uint32x8_serialize (select st #x1))
	         (concat (uint32x8_serialize (select st #x2))
	         (concat (uint32x8_serialize (select st #x3))
	         (concat (uint32x8_serialize (select st #x4))
	         (concat (uint32x8_serialize (select st #x5))
	         (concat (uint32x8_serialize (select st #x6))
	         (concat (uint32x8_serialize (select st #x7))
	         (concat (uint32x8_serialize (select st #x8))
	         (concat (uint32x8_serialize (select st #x9))
	         (concat (uint32x8_serialize (select st #xa))
	         (concat (uint32x8_serialize (select st #xb))
	         (concat (uint32x8_serialize (select st #xc))
	         (concat (uint32x8_serialize (select st #xd))
	         (concat (uint32x8_serialize (select st #xe))
	                 (uint32x8_serialize (select st #xf))))))))))))))))))))

(define-fun chacha20_block3 ((k key) (n nonce) (c counter)) block8
	         (chacha20_block3_state (setup k n c)))

;; Chacha20 Block Function RFC Test Vector
(define-fun key3 () block ((_ extract 4095 3584) (chacha20_block3 k n c)))
(assert (= key3 #x10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e))
(echo "Running vectorized chacha20_block3 RFC test:")
(check-sat)
(get-model)


(assert (forall ((m state))
        (= (chacha20_block_state m) ((_ extract 4095 3584) (chacha20_block3_state m)))))
(echo "Verifying chacha20_block_state = chacha_block3_state:")
(check-sat)
(get-model)

(assert (forall ((k key) (n nonce) (c counter))
        (= (chacha20_block k n c) ((_ extract 4095 3584) (chacha20_block3 k n c)))))

(echo "Verifying chacha20_block[0] = chacha_block3[0] :")
(check-sat)
(get-model)

(assert (forall ((k key) (n nonce) (c counter))
         (= (chacha20_block k n (bvadd c #x00000001)) 
            ((_ extract 3583 3072) (chacha20_block3 k n c)))))

(echo "Verifying chacha20_block[1] = chacha_block3[1] :")
(check-sat)
(get-model)

(assert (forall ((k key) (n nonce) (c counter))
        (= (chacha20_block k n (bvadd c #x00000010)) ((_ extract 3071 2560) (chacha20_block3 k n c)))))
(echo "Verifying chacha20_block[2] = chacha_block3[2] :")
(check-sat)
(get-model)

(assert (forall ((k key) (n nonce) (c counter))
        (= (chacha20_block k n (bvadd c #x00000011)) ((_ extract 2559 2048) (chacha20_block3 k n c)))))
(echo "Verifying chacha20_block[3] = chacha_block3[3] :")
(check-sat)
(get-model)

(assert (forall ((k key) (n nonce) (c counter))
        (= (chacha20_block k n (bvadd c #x00000100)) ((_ extract 2047 1536) (chacha20_block3 k n c)))))
(echo "Verifying chacha20_block[4] = chacha_block3[4] :")
(check-sat)
(get-model)

(assert (forall ((k key) (n nonce) (c counter))
        (= (chacha20_block k n (bvadd c #x00000101)) ((_ extract 1535 1024) (chacha20_block3 k n c)))))
(echo "Verifying chacha20_block[5] = chacha_block3[5] :")
(check-sat)
(get-model)

(assert (forall ((k key) (n nonce) (c counter))
        (= (chacha20_block k n (bvadd c #x00000110)) ((_ extract 1023 512) (chacha20_block3 k n c)))))
(echo "Verifying chacha20_block[6] = chacha_block3[6] :")
(check-sat)
(get-model)

(assert (forall ((k key) (n nonce) (c counter))
        (= (chacha20_block k n (bvadd c #x00000111)) ((_ extract 511 0) (chacha20_block3 k n c)))))

(echo "Verifying chacha20_block[7] = chacha_block3[7] :")
(check-sat)
(get-model)




