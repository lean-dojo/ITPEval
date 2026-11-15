;; Statement-only formalization of the ntp4vc corpus artifact
;; pearl/multiprecision/get_str_Get_str_wmpn_get_str_bitsqtvc: the verification
;; condition for converting a positive multiprecision integer to base 2^bits
;; digits in a writable byte buffer.  This file contains no proof.

(in-package "ACL2")

(defun gsb-bv8p (x)
  (and (integerp x) (<= 0 x) (< x 256)))

(defun gsb-bv32p (x)
  (and (integerp x) (<= 0 x) (< x 4294967296)))

(defun gsb-bv64p (x)
  (and (integerp x) (<= 0 x) (< x 18446744073709551616)))

(defun gsb-sint32 (x)
  (if (< x 2147483648) x (- x 4294967296)))

(defun gsb-int32-in-bounds-p (x)
  (and (integerp x) (<= -2147483648 x) (<= x 2147483647)))

(defun gsb-uint64-in-bounds-p (x)
  (and (integerp x) (<= 0 x) (<= x 18446744073709551615)))

(defun gsb-bv8-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and (gsb-bv8p (car xs))
         (gsb-bv8-list-p (cdr xs)))))

(defun gsb-bv64-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and (gsb-bv64p (car xs))
         (gsb-bv64-list-p (cdr xs)))))

(defun gsb-ptr8p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (car p) :ptr8)
       (gsb-bv8-list-p (cadr p))
       (integerp (caddr p))
       (integerp (cadddr p))
       (integerp (car (cddddr p)))
       (booleanp (cadr (cddddr p)))))

(defun gsb-ptr64p (p)
  (and (true-listp p)
       (equal (len p) 7)
       (equal (car p) :ptr64)
       (gsb-bv64-list-p (cadr p))
       (integerp (caddr p))
       (integerp (cadddr p))
       (integerp (car (cddddr p)))
       (booleanp (cadr (cddddr p)))))

(defun gsb-data (p) (cadr p))
(defun gsb-offset (p) (caddr p))
(defun gsb-min (p) (cadddr p))
(defun gsb-max (p) (car (cddddr p)))
(defun gsb-writable (p) (cadr (cddddr p)))
(defun gsb-zone (p) (caddr (cddddr p)))

(defun gsb-index (i)
  (if (and (integerp i) (< 0 i)) i 0))

(defun gsb-pelt8 (p i)
  (let ((n (gsb-index i)))
    (if (< n (len (gsb-data p)))
        (nth n (gsb-data p))
      0)))

(defun gsb-pelt64 (p i)
  (let ((n (gsb-index i)))
    (if (< n (len (gsb-data p)))
        (nth n (gsb-data p))
      0)))

(defun gsb-valid-p (p size)
  (and (gsb-int32-in-bounds-p size)
       (<= 0 size)
       (<= 0 (gsb-min p))
       (<= (gsb-min p) (gsb-offset p))
       (<= (+ (gsb-offset p) size) (gsb-max p))
       (<= (gsb-max p) (len (gsb-data p)))))

(defun gsb-ptr-bound-p (p i)
  (and (<= (gsb-min p) (+ (gsb-offset p) i))
       (< (+ (gsb-offset p) i) (gsb-max p))))

(defun gsb-ipow (base exponent)
  (expt base (nfix exponent)))

(defun gsb-tdiv (x y)
  (if (or (not (integerp x))
          (not (integerp y))
          (equal y 0))
      0
    (let ((q (floor (abs x) (abs y))))
      (if (< (* x y) 0) (- q) q))))

(defun gsb-tmod (x y)
  (- x (* y (gsb-tdiv x y))))

(defun gsb-value-count (p start count)
  (if (zp count)
      0
    (+ (gsb-pelt64 p start)
       (* 18446744073709551616
          (gsb-value-count p (+ 1 start) (- count 1))))))

(defun gsb-value (p size)
  (gsb-value-count p (gsb-offset p) (nfix size)))

(defun gsb-valueb (p nbits)
  (if (< nbits 0)
      0
    (let* ((i (floor nbits 64))
           (r (- nbits (* 64 i))))
      (+ (gsb-value p i)
         (* (gsb-ipow 18446744073709551616 i)
            (mod (gsb-pelt64 p (+ (gsb-offset p) i))
                 (gsb-ipow 2 r)))))))

(defun gsb-svalue-sub-count (base p start count)
  (if (zp count)
      0
    (+ (gsb-pelt8 p (+ start (- count 1)))
       (* base
          (gsb-svalue-sub-count base p start (- count 1))))))

(defun gsb-svalue-sub (base p n m)
  (gsb-svalue-sub-count base p n (nfix (- m n))))

(defun gsb-svalue (base p size)
  (gsb-svalue-sub base p (gsb-offset p) (+ (gsb-offset p) size)))

(defun-sk gsb-in-base-p (base p n m)
  (forall (k)
    (implies (and (integerp k) (<= n k) (< k m))
             (and (<= 0 (gsb-pelt8 p k))
                  (< (gsb-pelt8 p k) base)))))

(defun-sk gsb-frame-p (new old bound)
  (forall (k)
    (implies (and (integerp k)
                  (or (< k (gsb-offset new))
                      (<= (+ (gsb-offset new) bound) k)))
             (equal (gsb-pelt8 new k) (gsb-pelt8 old k)))))

(defun gsb-same-meta-p (p q)
  (and (equal (len (gsb-data p)) (len (gsb-data q)))
       (equal (gsb-offset p) (gsb-offset q))
       (equal (gsb-min p) (gsb-min q))
       (equal (gsb-max p) (gsb-max q))
       (equal (gsb-writable p) (gsb-writable q))
       (equal (gsb-zone p) (gsb-zone q))))

(defun-sk gsb-single-update-p (new old index byte)
  (forall (k)
    (implies (integerp k)
             (equal (gsb-pelt8 new k)
                    (if (equal k index)
                        byte
                      (gsb-pelt8 old k))))))

(defun gsb-loop-state-p (up bits original-sp un sn b shift j i sp1)
  (let ((done (* (- (gsb-sint32 sn) (gsb-sint32 j)) bits)))
    (and (<= 0 (gsb-sint32 i))
         (<= (gsb-sint32 i) (gsb-sint32 un))
         (<= 0 (gsb-sint32 j))
         (<= (gsb-sint32 j) (gsb-sint32 sn))
         (implies (< 0 (gsb-sint32 j))
                  (equal done (+ (* 64 (gsb-sint32 i)) shift)))
         (or (and (<= 0 shift) (< shift 64))
             (equal i un))
         (gsb-in-base-p b sp1
                        (+ (gsb-offset sp1) (gsb-sint32 j))
                        (+ (gsb-offset sp1) (gsb-sint32 sn)))
         (or (and (equal
                   (gsb-svalue-sub b sp1
                                   (+ (gsb-offset sp1) (gsb-sint32 j))
                                   (+ (gsb-offset sp1) (gsb-sint32 sn)))
                   (gsb-valueb up done))
                  (<= done (* 64 (gsb-sint32 un))))
             (and (equal (gsb-sint32 j) 0)
                  (equal (gsb-svalue b sp1 (gsb-sint32 sn))
                         (gsb-value up (gsb-sint32 un)))))
         (gsb-frame-p sp1 original-sp (gsb-sint32 sn)))))

(defun gsb-initial-state-p (up bits sp un sn b)
  (and (<= 0 0)
       (<= 0 (gsb-sint32 un))
       (<= 0 (gsb-sint32 sn))
       (<= (gsb-sint32 sn) (gsb-sint32 sn))
       (equal (* (- (gsb-sint32 sn) (gsb-sint32 sn)) bits) 0)
       (implies (< 0 (gsb-sint32 sn))
                (equal 0 (+ (* 64 0) 0)))
       (or (and (<= 0 0) (< 0 64))
           (equal 0 un))
       (gsb-in-base-p b sp
                      (+ (gsb-offset sp) (gsb-sint32 sn))
                      (+ (gsb-offset sp) (gsb-sint32 sn)))
       (or (and (equal
                 (gsb-svalue-sub b sp
                                 (+ (gsb-offset sp) (gsb-sint32 sn))
                                 (+ (gsb-offset sp) (gsb-sint32 sn)))
                 (gsb-valueb up 0))
                (<= 0 (* 64 (gsb-sint32 un))))
           (and (equal (gsb-sint32 sn) 0)
                (equal (gsb-svalue b sp (gsb-sint32 sn))
                       (gsb-value up (gsb-sint32 un)))))))

(defun gsb-after-write-p
  (up bits original-sp un sn b j o10 next-i next-shift sp2)
  (let* ((old-done (* (- (gsb-sint32 sn) (gsb-sint32 j)) bits))
         (new-done (+ old-done bits)))
    (and (< (gsb-sint32 o10) (gsb-sint32 j))
         (<= 0 (gsb-sint32 next-i))
         (<= (gsb-sint32 next-i) (gsb-sint32 un))
         (<= 0 (gsb-sint32 o10))
         (<= (gsb-sint32 o10) (gsb-sint32 sn))
         (equal (* (- (gsb-sint32 sn) (gsb-sint32 o10)) bits)
                new-done)
         (implies (< 0 (gsb-sint32 o10))
                  (equal new-done
                         (+ (* 64 (gsb-sint32 next-i)) next-shift)))
         (or (and (<= 0 next-shift) (< next-shift 64))
             (equal next-i un))
         (gsb-in-base-p b sp2
                        (+ (gsb-offset sp2) (gsb-sint32 o10))
                        (+ (gsb-offset sp2) (gsb-sint32 sn)))
         (or (and (equal
                   (gsb-svalue-sub b sp2
                                   (+ (gsb-offset sp2) (gsb-sint32 o10))
                                   (+ (gsb-offset sp2) (gsb-sint32 sn)))
                   (gsb-valueb up new-done))
                  (<= new-done (* 64 (gsb-sint32 un))))
             (and (equal (gsb-sint32 o10) 0)
                  (equal (gsb-svalue b sp2 (gsb-sint32 sn))
                         (gsb-value up (gsb-sint32 un)))))
         (gsb-frame-p sp2 original-sp (gsb-sint32 sn)))))

(defun-sk gsb-all-sp2-p
  (up bits original-sp un sn b j o10 next-i next-shift sp1 byte)
  (forall (sp2)
    (implies (gsb-ptr8p sp2)
             (implies
              (gsb-same-meta-p sp2 sp1)
              (implies
               (and (gsb-single-update-p
                     sp2 sp1
                     (+ (gsb-offset sp2) (gsb-sint32 o10))
                     byte)
                    (equal (gsb-pelt8
                            sp2
                            (+ (gsb-offset sp2) (gsb-sint32 o10)))
                           byte))
               (gsb-after-write-p up bits original-sp un sn b j o10
                                  next-i next-shift sp2))))))

(defun-sk gsb-all-bytes-p
  (up bits original-sp un sn b j o10 next-i next-shift sp1 sj)
  (forall (byte)
    (implies (gsb-bv8p byte)
             (implies
              (equal byte sj)
              (and (gsb-ptr-bound-p sp1 (gsb-sint32 o10))
                   (equal (gsb-writable sp1) t)
                   (gsb-all-sp2-p up bits original-sp un sn b j o10
                                  next-i next-shift sp1 byte))))))

(defun-sk gsb-all-sj-p
  (up bits original-sp un sn b j o10 next-i next-shift sp1 numerator)
  (forall (sj)
    (implies (gsb-bv64p sj)
             (implies
              (equal sj (gsb-tmod numerator b))
              (and (<= 0 sj)
                   (<= sj 255)
                   (gsb-all-bytes-p up bits original-sp un sn b j o10
                                    next-i next-shift sp1 sj))))))

(defun gsb-mod-digit-p
  (up bits original-sp un sn b j o10 next-i next-shift sp1 numerator)
  (and (not (equal b 0))
       (gsb-uint64-in-bounds-p (gsb-tmod numerator b))
       (gsb-all-sj-p up bits original-sp un sn b j o10
                     next-i next-shift sp1 numerator)))

(defun-sk gsb-all-o18-p
  (up bits original-sp un sn b j o10 o14 o15 sp1 o11 high)
  (forall (o18)
    (implies (gsb-bv64p o18)
             (implies
              (equal o18 (+ o11 high))
              (gsb-mod-digit-p up bits original-sp un sn b j o10
                               o14 o15 sp1 o18)))))

(defun-sk gsb-all-high-p
  (up bits original-sp un sn b j o10 o14 o15 sp1 o11 o17)
  (forall (high)
    (implies (gsb-bv64p high)
             (implies
              (equal high
                     (mod (* (gsb-pelt64
                              up (+ (gsb-offset up) (gsb-sint32 o14)))
                             (gsb-ipow 2 o17))
                          18446744073709551616))
              (and (gsb-uint64-in-bounds-p (+ o11 high))
                   (gsb-all-o18-p up bits original-sp un sn b j o10
                                    o14 o15 sp1 o11 high))))))

(defun-sk gsb-all-o17-p
  (up bits original-sp un sn b j o10 o14 o15 sp1 o11 o16)
  (forall (o17)
    (implies (gsb-bv64p o17)
             (implies
              (equal o17 (- o16 o15))
              (and (<= 0 o17)
                   (< o17 64)
                   (gsb-all-high-p up bits original-sp un sn b j o10
                                    o14 o15 sp1 o11 o17))))))

(defun-sk gsb-all-o16-p
  (up bits original-sp un sn b j o10 o14 o15 sp1 o11)
  (forall (o16)
    (implies (gsb-bv64p o16)
             (implies
              (equal o16 bits)
              (and (gsb-uint64-in-bounds-p (- o16 o15))
                   (gsb-all-o17-p up bits original-sp un sn b j o10
                                   o14 o15 sp1 o11 o16))))))

(defun-sk gsb-all-o15-p
  (up bits original-sp un sn b j o10 o14 o13 sp1 o11)
  (forall (o15)
    (implies (gsb-bv64p o15)
             (implies
              (equal o15 (- o13 64))
              (and (gsb-ptr-bound-p up (gsb-sint32 o14))
                   (gsb-all-o16-p up bits original-sp un sn b j o10
                                   o14 o15 sp1 o11))))))

(defun-sk gsb-all-o14-p
  (up bits original-sp un sn b j i o10 o13 sp1 o11)
  (forall (o14)
    (implies (gsb-bv32p o14)
             (implies
              (equal (gsb-sint32 o14) (+ (gsb-sint32 i) 1))
              (if (< (gsb-sint32 o14) (gsb-sint32 un))
                  (and (gsb-uint64-in-bounds-p (- o13 64))
                       (gsb-all-o15-p up bits original-sp un sn b j o10
                                       o14 o13 sp1 o11))
                (gsb-mod-digit-p up bits original-sp un sn b j o10
                                 o14 o13 sp1 o11))))))

(defun-sk gsb-all-o13-p
  (up bits original-sp un sn b j i o10 shift sp1 o11 o12)
  (forall (o13)
    (implies (gsb-bv64p o13)
             (implies
              (equal o13 (+ shift o12))
              (if (<= 64 o13)
                  (and (gsb-int32-in-bounds-p (+ (gsb-sint32 i) 1))
                       (gsb-all-o14-p up bits original-sp un sn b j i
                                       o10 o13 sp1 o11))
                (gsb-mod-digit-p up bits original-sp un sn b j o10
                                 i o13 sp1 o11))))))

(defun-sk gsb-all-o12-p
  (up bits original-sp un sn b j i o10 shift sp1 o11)
  (forall (o12)
    (implies (gsb-bv64p o12)
             (implies
              (equal o12 bits)
              (and (gsb-uint64-in-bounds-p (+ shift o12))
                   (gsb-all-o13-p up bits original-sp un sn b j i o10
                                   shift sp1 o11 o12))))))

(defun-sk gsb-all-o11-p
  (up bits original-sp un sn b j i o10 shift sp1)
  (forall (o11)
    (implies (gsb-bv64p o11)
             (implies
              (equal o11
                     (floor
                      (gsb-pelt64 up (+ (gsb-offset up) (gsb-sint32 i)))
                      (gsb-ipow 2 shift)))
              (and (not (equal (gsb-ipow 2 shift) 0))
                   (gsb-all-o12-p up bits original-sp un sn b j i o10
                                   shift sp1 o11))))))

(defun-sk gsb-all-o10-p
  (up bits original-sp un sn b shift j i sp1)
  (forall (o10)
    (implies (gsb-bv32p o10)
             (implies
              (equal (gsb-sint32 o10) (- (gsb-sint32 j) 1))
              (and (gsb-ptr-bound-p up (gsb-sint32 i))
                   (<= 0 shift)
                   (< shift 64)
                   (gsb-all-o11-p up bits original-sp un sn b j i o10
                                   shift sp1))))))

(defun gsb-positive-step-p
  (up bits original-sp un sn b shift j i sp1)
  (and (gsb-int32-in-bounds-p (- (gsb-sint32 j) 1))
       (gsb-all-o10-p up bits original-sp un sn b shift j i sp1)))

(defun-sk gsb-all-results-p (up bits original-sp un ub sn sp1)
  (forall (result)
    (implies (gsb-bv32p result)
             (implies
              (equal result (gsb-sint32 sn))
              (let ((alloc
                     (floor (+ (gsb-sint32 ub) bits -1) bits))
                    (base (gsb-ipow 2 bits)))
                (and (gsb-in-base-p base sp1
                                    (gsb-offset sp1)
                                    (+ (gsb-offset sp1) result))
                     (equal (gsb-svalue base sp1 result)
                            (gsb-value up (gsb-sint32 un)))
                     (< 0 result)
                     (<= result alloc)
                     (< 0
                        (gsb-pelt8 sp1 (gsb-offset sp1)))
                     (gsb-frame-p sp1 original-sp alloc)))))))

(defun gsb-loop-step-p
  (up bits original-sp un ub sn b shift j i sp1)
  (if (< 0 (gsb-sint32 j))
      (gsb-positive-step-p up bits original-sp un sn b shift j i sp1)
    (and (<= 0 (gsb-sint32 sn))
         (gsb-all-results-p up bits original-sp un ub sn sp1))))

(defun-sk gsb-all-loop-states-p (up bits sp un ub sn b)
  (forall (shift j i sp1)
    (implies
     (and (gsb-bv64p shift)
          (gsb-bv32p j)
          (gsb-bv32p i)
          (gsb-ptr8p sp1))
     (implies
      (gsb-same-meta-p sp1 sp)
      (implies
       (gsb-loop-state-p up bits sp un sn b shift j i sp1)
       (gsb-loop-step-p up bits sp un ub sn b shift j i sp1))))))

(defun gsb-for-b-p (up bits sp un ub sn b)
  (and (gsb-initial-state-p up bits sp un sn b)
       (gsb-all-loop-states-p up bits sp un ub sn b)))

(defun-sk gsb-all-b-p (up bits sp un ub sn o9)
  (forall (b)
    (implies (gsb-bv64p b)
             (implies
              (equal b (* (gsb-ipow 2 o9) 1))
              (gsb-for-b-p up bits sp un ub sn b)))))

(defun-sk gsb-all-o9-p (up bits sp un ub sn)
  (forall (o9)
    (implies (gsb-bv64p o9)
             (implies
              (equal o9 bits)
              (and (<= 0 o9)
                   (< o9 64)
                   (<= (* (gsb-ipow 2 o9) 1)
                       18446744073709551615)
                   (gsb-all-b-p up bits sp un ub sn o9))))))

(defun-sk gsb-all-sn-p (up bits sp un ub e o8)
  (forall (sn)
    (implies (gsb-bv32p sn)
             (implies
              (equal (gsb-sint32 sn)
                     (gsb-tdiv (gsb-sint32 e) (gsb-sint32 o8)))
              (gsb-all-o9-p up bits sp un ub sn)))))

(defun-sk gsb-all-o8-p (up bits sp un ub e)
  (forall (o8)
    (implies (gsb-bv32p o8)
             (implies
              (equal (gsb-sint32 o8) bits)
              (and (not (equal (gsb-sint32 o8) 0))
                   (gsb-int32-in-bounds-p
                    (gsb-tdiv (gsb-sint32 e) (gsb-sint32 o8)))
                   (gsb-all-sn-p up bits sp un ub e o8))))))

(defun-sk gsb-all-e-p (up bits sp un ub o7)
  (forall (e)
    (implies (gsb-bv32p e)
             (implies
              (equal (gsb-sint32 e) (- (gsb-sint32 o7) 1))
              (and (<= bits 2147483647)
                   (gsb-all-o8-p up bits sp un ub e))))))

(defun-sk gsb-all-o7-p (up bits sp un ub o6 o2)
  (forall (o7)
    (implies (gsb-bv32p o7)
             (implies
              (equal (gsb-sint32 o7)
                     (+ (gsb-sint32 o6) (gsb-sint32 o2)))
              (and (gsb-int32-in-bounds-p (- (gsb-sint32 o7) 1))
                   (gsb-all-e-p up bits sp un ub o7))))))

(defun-sk gsb-all-o6-p (up bits sp un ub o5 o3 o2)
  (forall (o6)
    (implies (gsb-bv32p o6)
             (implies
              (equal (gsb-sint32 o6)
                     (+ (gsb-sint32 o5) (gsb-sint32 o3)))
              (and (gsb-int32-in-bounds-p
                    (+ (gsb-sint32 o6) (gsb-sint32 o2)))
                   (gsb-all-o7-p up bits sp un ub o6 o2))))))

(defun-sk gsb-all-o5-p (up bits sp un ub o4 o3 o2)
  (forall (o5)
    (implies (gsb-bv32p o5)
             (implies
              (equal (gsb-sint32 o5) (* 64 (gsb-sint32 o4)))
              (and (gsb-int32-in-bounds-p
                    (+ (gsb-sint32 o5) (gsb-sint32 o3)))
                   (gsb-all-o6-p up bits sp un ub o5 o3 o2))))))

(defun-sk gsb-all-o4-p (up bits sp un ub o3 o2)
  (forall (o4)
    (implies (gsb-bv32p o4)
             (implies
              (equal (gsb-sint32 o4) (- (gsb-sint32 un) 1))
              (and (gsb-int32-in-bounds-p (* 64 (gsb-sint32 o4)))
                   (gsb-all-o5-p up bits sp un ub o4 o3 o2))))))

(defun-sk gsb-all-o3-p (up bits sp un ub sb o2)
  (forall (o3)
    (implies (gsb-bv32p o3)
             (implies
              (equal (gsb-sint32 o3) sb)
              (and (gsb-int32-in-bounds-p (- (gsb-sint32 un) 1))
                   (gsb-all-o4-p up bits sp un ub o3 o2))))))

(defun-sk gsb-all-o2-p (up bits sp un ub sb)
  (forall (o2)
    (implies (gsb-bv32p o2)
             (implies
              (equal (gsb-sint32 o2) bits)
              (and (<= sb 2147483647)
                   (gsb-all-o3-p up bits sp un ub sb o2))))))

(defun-sk gsb-all-sb-p (up bits sp un ub um)
  (forall (sb)
    (implies
     (gsb-bv64p sb)
     (implies
      (and (<= 1 sb)
           (<= sb 64)
           (<= (gsb-ipow 2 (- sb 1)) um)
           (< um (gsb-ipow 2 sb)))
      (and (<= bits 2147483647)
           (gsb-all-o2-p up bits sp un ub sb))))))

(defun-sk gsb-all-o1-p (up bits sp un ub)
  (forall (o1)
    (implies
     (gsb-bv32p o1)
     (implies
      (equal (gsb-sint32 o1) (- (gsb-sint32 un) 1))
      (let ((um (gsb-pelt64
                 up (+ (gsb-offset up) (gsb-sint32 o1)))))
        (and (gsb-ptr-bound-p up (gsb-sint32 o1))
             (< 0 um)
             (gsb-all-sb-p up bits sp un ub um)))))))

(defun get-str-get-str-wmpn-get-str-bits-statement
  (un up bits sp ub)
  (implies
   (and (gsb-bv32p un)
        (gsb-ptr64p up)
        (gsb-bv32p bits)
        (gsb-ptr8p sp)
        (gsb-bv32p ub)
        (<= 1 (gsb-sint32 un))
        (gsb-valid-p up (gsb-sint32 un))
        (<= 1 bits)
        (<= bits 8)
        (gsb-valid-p sp
                     (floor (+ (gsb-sint32 ub) bits -1) bits))
        (<= 0 (gsb-sint32 ub))
        (< (gsb-value up (gsb-sint32 un))
           (gsb-ipow 2 (gsb-sint32 ub)))
        (< 0 (gsb-pelt64
              up (+ (gsb-offset up) (gsb-sint32 un) -1)))
        (<= (+ (* 64 (gsb-sint32 un)) 7) 2147483647)
        (equal (gsb-writable sp) t))
   (and (gsb-int32-in-bounds-p (- (gsb-sint32 un) 1))
        (gsb-all-o1-p up bits sp un ub))))

(value-triple :itpeval-statement-checked)
:q
